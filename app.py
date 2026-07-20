from __future__ import annotations

import io
import itertools
import json
import math
import re
import time
import unicodedata
import urllib.request
import urllib.parse
import xml.etree.ElementTree as ET
from email.utils import parsedate_to_datetime
from datetime import datetime
from html import unescape
from pathlib import Path

import dash
from dash import Dash, Input, Output, State, dash_table, dcc, html, no_update
import dash_bootstrap_components as dbc
import numpy as np
import pandas as pd
import plotly.graph_objects as go
import plotly.express as px

BASE_DIR = Path(__file__).resolve().parent
DATA_DIR = BASE_DIR / "data"
GEOBOUNDARIES_API = "https://www.geoboundaries.org/api/current/gbOpen/PRT/{adm}/"

CHAIN_COLORS = {
    "Alcampo": "#f97316",
    "Carrefour": "#2563eb",
    "Dia": "#dc2626",
    "Lidl": "#7c3aed",
    "Mercadona": "#16a34a",
}
DEFAULT_RADIUS = 500
ALIMARKET_RSS_FEEDS = [
    "https://www.alimarket.es/media/rss/alimentacion.xml",
    "https://www.alimarket.es/media/rss/sectores/alimentacion-sector-distribucion-base-alimentaria.xml",
    "https://www.alimarket.es/media/rss/sectores/alimentacion-sector-alimentacion-y-bebidas.xml",
    "https://www.alimarket.es/media/rss/sectores/alimentacion-sector-gran-consumo.xml",
    "https://www.alimarket.es/media/rss/sectores/alimentacion-tiendas-de-conveniencia.xml",
    "https://www.alimarket.es/media/rss/sectores/alimentacion-ecommerce-de-alimentacion.xml",
    "https://www.alimarket.es/media/rss/sectores/alimentacion-coyuntura.xml",
    "https://www.alimarket.es/media/rss/sectores/alimentacion-equipamiento-comercial.xml",
]
ALIMARKET_REPORT = "https://www.alimarket.es/alimentacion/informe/421975/informe-2026-sobre-la-distribucion-alimentaria-en-espana-por-superficie/informe-completo"
ALIMARKET_FOOD_HOME = "https://www.alimarket.es/alimentacion"
DATA_QUALITY_REPORT: list[dict] = []
ESP_ADM2_PATH = DATA_DIR / "geoboundaries_esp_adm2_simplified.geojson"
ESP_ADM2_GEOJSON = json.loads(ESP_ADM2_PATH.read_text(encoding="utf-8")) if ESP_ADM2_PATH.exists() else None


def volta_candidates() -> pd.DataFrame:
    """Combine store points with the cadastral checks already completed."""
    columns = [
        "cadeia", "nome", "morada", "municipio", "latitude", "longitude",
        "referencia_cadastral", "uso_cadastral", "area_edificio_m2",
        "contexto", "status_volta", "motivo", "fonte_area",
    ]
    stores = DF[["cadeia", "nome", "morada", "municipio", "latitude", "longitude"]].copy()
    stores["coord_key"] = stores["latitude"].round(6).astype(str) + "|" + stores["longitude"].round(6).astype(str)
    source = DATA_DIR / "candidatos_volta.csv"
    if source.exists():
        checks = pd.DataFrame()
        for attempt in range(3):
            try:
                checks = pd.read_csv(source)
                break
            except (pd.errors.EmptyDataError, pd.errors.ParserError, PermissionError):
                if attempt == 2:
                    raise
                time.sleep(0.15)
        checks["coord_key"] = checks["latitude"].round(6).astype(str) + "|" + checks["longitude"].round(6).astype(str)
        checks = checks.drop(columns=["cadeia", "latitude", "longitude"], errors="ignore")
        stores = stores.merge(checks, on="coord_key", how="left")
    for col in columns:
        if col not in stores:
            stores[col] = np.nan if col == "area_edificio_m2" else ""
    def classify_volta(row):
        current = clean_text(row.get("status_volta"))
        if current:
            return current
        area = row.get("area_edificio_m2")
        if pd.isna(area):
            return "Verificar"
        if float(area) < 400:
            return "Improvável"
        if float(area) > 5000:
            return "Centro comercial"
        return "Provável"

    stores["status_volta"] = stores.apply(classify_volta, axis=1)
    stores["contexto"] = stores["contexto"].fillna("Não classificado")
    stores["motivo"] = stores["motivo"].fillna("Área cadastral ainda por pesquisar")
    stores["fonte_area"] = stores["fonte_area"].fillna("")
    stores["referencia_cadastral"] = stores["referencia_cadastral"].fillna("")
    stores["uso_cadastral"] = stores["uso_cadastral"].fillna("")
    return stores[columns]


def load_market_news(limit: int = 12) -> list[dict]:
    """Read public RSS metadata without reproducing subscriber-only content."""
    items, seen = [], set()
    for feed_url in ALIMARKET_RSS_FEEDS:
        request = urllib.request.Request(feed_url, headers={"User-Agent": "GeomarketingDashboard/1.0"})
        try:
            with urllib.request.urlopen(request, timeout=5) as response:
                root = ET.fromstring(response.read())
            for item in root.findall(".//item"):
                title = clean_text(item.findtext("title"))
                link = clean_text(item.findtext("link"))
                summary = clean_text(item.findtext("description"))
                raw_date = clean_text(item.findtext("pubDate"))
                if not title or not link or link in seen:
                    continue
                try:
                    parsed_date = parsedate_to_datetime(raw_date)
                    if parsed_date is None:
                        raise ValueError("Data RSS vazia")
                    date = parsed_date.strftime("%d/%m/%Y")
                    sort_date = parsed_date.timestamp()
                except Exception:
                    try:
                        parsed_date = datetime.fromisoformat(raw_date)
                        date = parsed_date.strftime("%d/%m/%Y")
                        sort_date = parsed_date.timestamp()
                    except Exception:
                        date, sort_date = raw_date, 0
                seen.add(link)
                items.append({"title": title, "link": link, "summary": summary[:280], "date": date, "sort_date": sort_date})
        except Exception:
            continue
    return sorted(items, key=lambda item: item["sort_date"], reverse=True)[:limit]


def load_featured_food_news(limit: int = 9) -> list[dict]:
    """Extract public headline metadata from 'Destacado en Alimentación'."""
    request = urllib.request.Request(ALIMARKET_FOOD_HOME, headers={"User-Agent": "Mozilla/5.0 GeomarketingDashboard/1.0"})
    try:
        with urllib.request.urlopen(request, timeout=8) as response:
            page = response.read().decode("utf-8", errors="ignore")
        start = page.find("Destacado en Alimentaci")
        if start < 0:
            return []
        end = page.find("</section>", start)
        section = page[start:end if end > start else start + 60000]
        pattern = re.compile(
            r'<h1[^>]*itemprop="headline"[^>]*>\s*<a href="([^"]+)"[^>]*>(.*?)</a>\s*</h1>\s*'
            r'<meta[^>]*itemprop="dateCreated datePublished"[^>]*content="([^"]+)"',
            re.I | re.S,
        )
        items = []
        for link, title, raw_date in pattern.findall(section)[:limit]:
            title = clean_text(unescape(title))
            link = urllib.parse.urljoin(ALIMARKET_FOOD_HOME, unescape(link))
            try:
                date = datetime.fromisoformat(raw_date).strftime("%d/%m/%Y")
            except Exception:
                date = raw_date
            if title and link:
                items.append({"title": title, "link": link, "summary": "", "date": date, "sort_date": 0})
        return items
    except Exception:
        return []


def clean_text(x: object) -> str:
    if x is None or (isinstance(x, float) and pd.isna(x)):
        return ""
    s = str(x)
    if "Ã" in s or "Â" in s:
        try:
            s = s.encode("latin1").decode("utf-8")
        except Exception:
            pass
    s = re.sub(r"<br\s*/?>", " ", s, flags=re.I)
    s = re.sub(r"<[^>]+>", " ", s)
    s = s.replace("&amp;", "&")
    s = re.sub(r"\s+", " ", s).strip()
    if s.lower() in {"nan", "none", "null"}:
        return ""
    return s


def normalized_series(series: pd.Series) -> pd.Series:
    """Lowercase/ascii representation used only for brand validation."""
    return series.fillna("").astype(str).map(
        lambda value: unicodedata.normalize("NFKD", value)
        .encode("ascii", "ignore")
        .decode("ascii")
        .strip()
        .lower()
    )


def filter_source_rows(raw: pd.DataFrame, cadeia: str, source: str) -> pd.DataFrame:
    """Remove cross-brand contamination while retaining agreed store formats."""
    brand = normalized_series(raw["marca"] if "marca" in raw else raw.get("brand", pd.Series(index=raw.index, dtype=str)))
    name_col = next((c for c in ("nome", "name", "storeName") if c in raw.columns), None)
    name = normalized_series(raw[name_col] if name_col else pd.Series(index=raw.index, dtype=str))
    category = normalized_series(raw["category"] if "category" in raw else pd.Series(index=raw.index, dtype=str))

    if cadeia == "Alcampo":
        valid = brand.str.fullmatch(r"alcampo") | ((brand == "") & name.str.contains(r"\balcampo\b|\bmialcampo\b", regex=True))
        valid &= ~name.str.contains(r"\bdia\b|mercadona|carrefour|\blidl\b", regex=True)
    elif cadeia == "Dia":
        valid_brands = {"dia", "dia market", "maxi dia", "la plaza de dia"}
        valid = brand.isin(valid_brands) | ((brand == "") & name.str.contains(r"\bdia\b", regex=True))
        valid &= ~name.str.contains(r"alcampo|mercadona|carrefour|\blidl\b", regex=True)
    elif cadeia == "Mercadona":
        valid = brand.eq("mercadona") | ((brand == "") & name.str.fullmatch(r"mercadona"))
        valid &= ~name.str.contains(r"alcampo|carrefour|\blidl\b|\bdia\b", regex=True)
    elif cadeia == "Carrefour":
        # Express CEPSA, convenience formats and service-station shops are competitors.
        valid = ~category.eq("agencia de viajes")
    elif cadeia == "Lidl":
        valid = pd.Series(True, index=raw.index)
    else:
        valid = pd.Series(False, index=raw.index)

    removed = int((~valid).sum())
    DATA_QUALITY_REPORT.append({"ficheiro": source, "cadeia": cadeia, "tipo": "marca/categoria inválida", "registos": removed})
    return raw.loc[valid].copy()


def clean_coord(value: object, kind: str, lat_for_lon: float | None = None) -> float | None:
    try:
        if value is None or (isinstance(value, float) and pd.isna(value)):
            return None
        s = str(value).strip().replace(",", ".")
        if not s or s.lower() == "nan":
            return None
        v = float(s)
    except Exception:
        return None

    if kind == "lat":
        if -90 <= v <= 90:
            return v
        return None

    # longitude corrections for common malformed CSV values, e.g. -8073513 -> -8.073513
    if abs(v) > 180:
        digits = re.sub(r"[^0-9]", "", str(value))
        if digits:
            sign = -1 if str(value).strip().startswith("-") else 1
            for denom in (1e6, 1e7, 1e8):
                cand = sign * (float(digits) / denom)
                if -32 <= cand <= -5:
                    return cand
    if -32 <= v <= -5:
        return v
    if -180 <= v <= 180:
        return v
    return None


def google_streetview_url(lat: float, lon: float) -> str:
    return f"https://www.google.com/maps/@?api=1&map_action=pano&viewpoint={lat:.7f},{lon:.7f}"


def apple_lookaround_url(lat: float, lon: float) -> str:
    # Opens Apple Maps centered at the coordinate; where Apple Look Around exists, user can enter Look Around.
    return f"https://maps.apple.com/?ll={lat:.7f},{lon:.7f}&q=Look%20Around"


def geoboundaries_cache_path(adm: str, simplified: bool = True) -> Path:
    suffix = "simplified" if simplified else "full"
    return DATA_DIR / f"geoboundaries_prt_{adm.lower()}_{suffix}.geojson"


def download_geoboundaries(adm: str, simplified: bool = True) -> dict | None:
    """Download and cache Portugal boundaries from geoBoundaries."""
    cache_path = geoboundaries_cache_path(adm, simplified)
    if cache_path.exists():
        try:
            return json.loads(cache_path.read_text(encoding="utf-8"))
        except Exception:
            pass

    try:
        with urllib.request.urlopen(GEOBOUNDARIES_API.format(adm=adm), timeout=30) as response:
            meta = json.loads(response.read().decode("utf-8"))
        if simplified:
            geojson_url = meta.get("simplifiedGeometryGeoJSON") or meta.get("gjDownloadURL")
        else:
            geojson_url = meta.get("gjDownloadURL") or meta.get("simplifiedGeometryGeoJSON")
        if not geojson_url:
            return None
        with urllib.request.urlopen(geojson_url, timeout=60) as response:
            data = json.loads(response.read().decode("utf-8"))
        cache_path.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
        return data
    except Exception:
        return None


def iter_rings(geometry: dict):
    if not geometry:
        return
    geom_type = geometry.get("type")
    coords = geometry.get("coordinates") or []
    if geom_type == "Polygon":
        for ring in coords:
            yield ring
    elif geom_type == "MultiPolygon":
        for polygon in coords:
            for ring in polygon:
                yield ring


def iter_polygons(geometry: dict):
    if not geometry:
        return
    geom_type = geometry.get("type")
    coords = geometry.get("coordinates") or []
    if geom_type == "Polygon":
        yield coords
    elif geom_type == "MultiPolygon":
        for polygon in coords:
            yield polygon


def point_in_ring(lon: float, lat: float, ring: list) -> bool:
    inside = False
    if len(ring) < 3:
        return False
    x1, y1 = ring[-1][0], ring[-1][1]
    for point in ring:
        x2, y2 = point[0], point[1]
        crosses = (y1 > lat) != (y2 > lat)
        if crosses:
            x_at_lat = (x2 - x1) * (lat - y1) / ((y2 - y1) or 1e-12) + x1
            if lon < x_at_lat:
                inside = not inside
        x1, y1 = x2, y2
    return inside


def point_in_geometry(lon: float, lat: float, geometry: dict) -> bool:
    for polygon in iter_polygons(geometry) or []:
        if not polygon:
            continue
        if point_in_ring(lon, lat, polygon[0]) and not any(point_in_ring(lon, lat, hole) for hole in polygon[1:]):
            return True
    return False


def prepared_boundaries(adm: str) -> list[dict]:
    data = download_geoboundaries(adm, simplified=False)
    if not data:
        return []
    boundaries = []
    for feature in data.get("features", []):
        rings = list(iter_rings(feature.get("geometry")))
        points = [point for ring in rings for point in ring]
        if not points:
            continue
        lons = [point[0] for point in points]
        lats = [point[1] for point in points]
        boundaries.append(
            {
                "name": clean_text(feature.get("properties", {}).get("shapeName", "")),
                "geometry": feature.get("geometry"),
                "bbox": (min(lons), min(lats), max(lons), max(lats)),
            }
        )
    return boundaries


def locate_boundary(lat: float, lon: float, boundaries: list[dict]) -> str:
    bbox_candidates = []
    for boundary in boundaries:
        min_lon, min_lat, max_lon, max_lat = boundary["bbox"]
        if min_lon <= lon <= max_lon and min_lat <= lat <= max_lat:
            if point_in_geometry(lon, lat, boundary["geometry"]):
                return boundary["name"]
            area = (max_lon - min_lon) * (max_lat - min_lat)
            bbox_candidates.append((area, boundary["name"]))
    if bbox_candidates:
        return sorted(bbox_candidates, key=lambda item: item[0])[0][1]
    return ""


def infer_boundary_from_text(text: str, boundaries: list[dict]) -> str:
    normalized = f" {normalize_boundary_text(text)} "
    matches = []
    for boundary in boundaries:
        name = normalize_boundary_text(boundary["name"])
        if name and f" {name} " in normalized:
            matches.append((len(name), boundary["name"]))
    if matches:
        return sorted(matches, reverse=True)[0][1]
    return ""


def normalize_boundary_text(value: object) -> str:
    value = unicodedata.normalize("NFKD", str(value or "")).encode("ascii", "ignore").decode("ascii")
    value = re.sub(r"[^a-zA-Z0-9]+", " ", value.lower())
    return re.sub(r"\s+", " ", value).strip()


def nearest_boundary(lat: float, lon: float, boundaries: list[dict]) -> str:
    best = None
    for boundary in boundaries:
        min_lon, min_lat, max_lon, max_lat = boundary["bbox"]
        center_lat = (min_lat + max_lat) / 2
        center_lon = (min_lon + max_lon) / 2
        score = (lat - center_lat) ** 2 + ((lon - center_lon) * math.cos(math.radians(lat))) ** 2
        if best is None or score < best[0]:
            best = (score, boundary["name"])
    return best[1] if best else ""


def enrich_with_admin_boundaries(df: pd.DataFrame) -> pd.DataFrame:
    """Fill municipio/distrito from coordinates using geoBoundaries ADM2/ADM1."""
    if df.empty:
        return df
    municipios = prepared_boundaries("ADM2")
    distritos = prepared_boundaries("ADM1")
    if not municipios and not distritos:
        return df

    out = df.copy()
    geo_municipios = []
    geo_distritos = []
    for row in out.itertuples(index=False):
        lat = float(row.latitude)
        lon = float(row.longitude)
        municipio = locate_boundary(lat, lon, municipios) if municipios else ""
        if not municipio and municipios:
            municipio = infer_boundary_from_text(f"{row.nome} {row.morada}", municipios)
        if not municipio and municipios:
            municipio = nearest_boundary(lat, lon, municipios)
        geo_municipios.append(municipio)
        geo_distritos.append(locate_boundary(lat, lon, distritos) if distritos else "")

    out["municipio_geo"] = geo_municipios
    out["distrito_geo"] = geo_distritos
    out["municipio"] = np.where(out["municipio_geo"] != "", out["municipio_geo"], out["municipio"])
    out["distrito"] = np.where(out["distrito_geo"] != "", out["distrito_geo"], out["distrito"])
    out = out.drop(columns=["municipio_geo", "distrito_geo"])
    return out


def normalize_file(path: Path) -> pd.DataFrame:
    raw = pd.read_csv(path)
    fname = path.stem.lower()
    chain_names = {
        "alcampo": "Alcampo",
        "carrefour": "Carrefour",
        "dia": "Dia",
        "lidl_espanha_lojas": "Lidl",
        "mercadona": "Mercadona",
    }
    if fname not in chain_names:
        return pd.DataFrame()
    cadeia = chain_names[fname]
    raw = filter_source_rows(raw, cadeia, path.name)
    cols = {c.lower(): c for c in raw.columns}

    def pick(*names):
        for name in names:
            if name in cols:
                return raw[cols[name]]
        return pd.Series([""] * len(raw), index=raw.index)

    df = pd.DataFrame({
        "id": pick("id", "osm_id", "objectnumber", "codsa"),
        "nome": pick("nome", "name", "titulo", "storename"),
        "morada": pick("morada", "morada_completa", "address", "address.streetname"),
        "codigo_postal": pick("cp", "postalcode", "codigo_postal", "postal", "address.zip"),
        "municipio": pick("municipio", "city", "cidade", "concelho", "address.city"),
        "distrito": pick("distrito", "zone", "estado", "state", "address.state"),
        "telefone": pick("telefone", "phone"),
        "email": pick("email"),
        "horario": pick("horario", "horarios", "hours", "hours1", "openinghours.items"),
        "servicos": pick("servico", "servicos", "features", "marketingdata.infoicons"),
        "latitude": pick("latitude", "lat", "address.latitude"),
        "longitude": pick("longitude", "lng", "lon", "address.longitude"),
    })

    if "address.streetname" in cols:
        street = raw[cols["address.streetname"]].fillna("").astype(str)
        number = pick("address.streetnumber").fillna("").astype(str)
        df["morada"] = (street + " " + number).str.strip()

    df["cadeia"] = cadeia
    for c in ["nome", "morada", "codigo_postal", "municipio", "distrito", "telefone", "email", "horario", "servicos"]:
        df[c] = df[c].apply(clean_text)
    lat = [clean_coord(x, "lat") for x in df["latitude"]]
    lon = [clean_coord(x, "lon", la) for x, la in zip(df["longitude"], lat)]
    df["latitude"] = lat
    df["longitude"] = lon
    df = df.dropna(subset=["latitude", "longitude"]).copy()
    # Península Ibérica, Baleares, Canárias e arquipélagos portugueses.
    df = df[(df["latitude"].between(25, 46)) & (df["longitude"].between(-32, 6))].copy()
    df["coord_key"] = df["latitude"].round(6).astype(str) + "|" + df["longitude"].round(6).astype(str)
    duplicate_mask = df.duplicated("coord_key", keep=False)
    conflicting = 0
    if duplicate_mask.any():
        conflicting = int(
            df.loc[duplicate_mask]
            .groupby("coord_key")["municipio"]
            .nunique()
            .gt(1)
            .sum()
        )
    duplicate_rows = int(df.duplicated("coord_key", keep="first").sum())
    DATA_QUALITY_REPORT.append({"ficheiro": path.name, "cadeia": cadeia, "tipo": "duplicados por coordenada removidos", "registos": duplicate_rows})
    DATA_QUALITY_REPORT.append({"ficheiro": path.name, "cadeia": cadeia, "tipo": "coordenadas com cidades incompatíveis", "registos": conflicting})
    df = df.drop_duplicates("coord_key", keep="first").drop(columns="coord_key")
    df["street_view"] = [google_streetview_url(a, b) for a, b in zip(df.latitude, df.longitude)]
    df["apple_lookaround"] = [apple_lookaround_url(a, b) for a, b in zip(df.latitude, df.longitude)]
    df["coords"] = df.apply(lambda r: f"{r.latitude:.6f}, {r.longitude:.6f}", axis=1)
    return df.reset_index(drop=True)


def load_data() -> pd.DataFrame:
    frames = []
    for p in sorted(DATA_DIR.glob("*.csv")):
        frames.append(normalize_file(p))
    if not frames:
        return pd.DataFrame()
    df = pd.concat(frames, ignore_index=True)
    df["row_id"] = np.arange(len(df))
    return df


DF = load_data()
CHAINS = sorted(DF["cadeia"].unique().tolist())

# Todas as combinações únicas entre cadeias, sem duplicar A x B / B x A.
ALLOWED_INTERSECTION_PAIRS = list(itertools.combinations(CHAINS, 2))
PAIR_OPTIONS = ["Todas"] + [f"{a} x {b}" for a, b in ALLOWED_INTERSECTION_PAIRS]


def hdist_m(lat1, lon1, lat2, lon2):
    R = 6371000.0
    p1 = np.radians(lat1)
    p2 = np.radians(lat2)
    dp = np.radians(np.asarray(lat2) - lat1)
    dl = np.radians(np.asarray(lon2) - lon1)
    a = np.sin(dp / 2) ** 2 + np.cos(p1) * np.cos(p2) * np.sin(dl / 2) ** 2
    return 2 * R * np.arcsin(np.sqrt(a))


def intersection_pairs(chain_a: str, chain_b: str, radius: int, max_rows: int = 5000) -> pd.DataFrame:
    """Return pairs from two different chains within radius meters.

    radius == 0 is treated as exact same coordinate after 6 decimal rounding.
    This is useful to identify the same physical point / same geocoded location.
    """
    radius = int(radius or 0)
    a = DF[DF.cadeia == chain_a].reset_index(drop=True)
    b = DF[DF.cadeia == chain_b].reset_index(drop=True)
    if a.empty or b.empty:
        return pd.DataFrame()

    rows = []

    if radius <= 0:
        bb = b.copy()
        bb["coord_key"] = bb.apply(lambda r: f"{float(r.latitude):.6f}|{float(r.longitude):.6f}", axis=1)
        lookup = {k: g for k, g in bb.groupby("coord_key")}
        for _, ra in a.iterrows():
            key = f"{float(ra.latitude):.6f}|{float(ra.longitude):.6f}"
            if key not in lookup:
                continue
            for _, rb in lookup[key].iterrows():
                rows.append({
                    "row_id_a": int(ra.row_id) if "row_id" in ra.index else int(ra.name),
                    "cadeia_a": str(chain_a),
                    "loja_a": str(ra.nome),
                    "morada_a": str(ra.morada),
                    "municipio_a": str(ra.municipio),
                    "distrito_a": str(ra.distrito),
                    "lat_a": float(ra.latitude),
                    "lon_a": float(ra.longitude),
                    "row_id_b": int(rb.row_id) if "row_id" in rb.index else int(rb.name),
                    "cadeia_b": str(chain_b),
                    "loja_b": str(rb.nome),
                    "morada_b": str(rb.morada),
                    "municipio_b": str(rb.municipio),
                    "distrito_b": str(rb.distrito),
                    "lat_b": float(rb.latitude),
                    "lon_b": float(rb.longitude),
                    "dist_m": 0.0,
                    "street_view_a": str(ra.street_view),
                    "apple_lookaround_a": str(ra.apple_lookaround),
                    "street_view_b": str(rb.street_view),
                    "apple_lookaround_b": str(rb.apple_lookaround),
                })
                if len(rows) >= max_rows:
                    break
            if len(rows) >= max_rows:
                break
    else:
        b_lat = b.latitude.to_numpy(dtype=float)
        b_lon = b.longitude.to_numpy(dtype=float)
        for _, ra in a.iterrows():
            lat0 = float(ra.latitude)
            lon0 = float(ra.longitude)
            lat_delta = radius / 111_320.0
            lon_delta = radius / max(111_320.0 * math.cos(math.radians(lat0)), 1.0)
            candidates = np.where(
                (np.abs(b_lat - lat0) <= lat_delta) &
                (np.abs(b_lon - lon0) <= lon_delta)
            )[0]
            if not len(candidates):
                continue
            d = hdist_m(lat0, lon0, b_lat[candidates], b_lon[candidates])
            local_matches = np.where(d <= radius)[0]
            for local_idx in local_matches:
                j = int(candidates[local_idx])
                rb = b.iloc[int(j)]
                rows.append({
                    "row_id_a": int(ra.row_id) if "row_id" in ra.index else int(ra.name),
                    "cadeia_a": str(chain_a),
                    "loja_a": str(ra.nome),
                    "morada_a": str(ra.morada),
                    "municipio_a": str(ra.municipio),
                    "distrito_a": str(ra.distrito),
                    "lat_a": float(ra.latitude),
                    "lon_a": float(ra.longitude),
                    "row_id_b": int(rb.row_id) if "row_id" in rb.index else int(rb.name),
                    "cadeia_b": str(chain_b),
                    "loja_b": str(rb.nome),
                    "morada_b": str(rb.morada),
                    "municipio_b": str(rb.municipio),
                    "distrito_b": str(rb.distrito),
                    "lat_b": float(rb.latitude),
                    "lon_b": float(rb.longitude),
                    "dist_m": float(d[local_idx]),
                    "street_view_a": str(ra.street_view),
                    "apple_lookaround_a": str(ra.apple_lookaround),
                    "street_view_b": str(rb.street_view),
                    "apple_lookaround_b": str(rb.apple_lookaround),
                })
                if len(rows) >= max_rows:
                    break
            if len(rows) >= max_rows:
                break

    out = pd.DataFrame(rows)
    if not out.empty:
        out = out.sort_values("dist_m", kind="stable").reset_index(drop=True)
    return out

def all_intersections(radius: int, pair_value: str) -> pd.DataFrame:
    if pair_value != "Todas":
        a, b = pair_value.split(" x ")
        return intersection_pairs(a, b, radius)
    frames = []
    for a, b in ALLOWED_INTERSECTION_PAIRS:
        x = intersection_pairs(a, b, radius, max_rows=3000)
        if not x.empty:
            frames.append(x)
    return pd.concat(frames, ignore_index=True) if frames else pd.DataFrame()


def nearest_competition(df: pd.DataFrame, radius: int = DEFAULT_RADIUS) -> pd.DataFrame:
    rows = []
    for i, r in df.iterrows():
        other = df[df.cadeia != r.cadeia]
        if other.empty:
            rows.append((np.nan, "", 0))
            continue
        d = hdist_m(r.latitude, r.longitude, other.latitude.to_numpy(), other.longitude.to_numpy())
        if len(d) == 0:
            rows.append((np.nan, "", 0))
            continue
        j = int(np.argmin(d))
        rows.append((float(d[j]), other.iloc[j].cadeia, int((d <= radius).sum())))
    out = df.copy()
    out[["dist_concorrente_m", "concorrente_mais_proximo", "concorrentes_no_raio"]] = pd.DataFrame(rows, index=out.index)
    return out



def competition_dataset(base_chain: str = "Todas", competitor_chain: str = "Todas", radius: int = DEFAULT_RADIUS) -> pd.DataFrame:
    """One row per base store with closest competitor and competitors in radius.

    radius == 0 means exact same coordinate (rounded to 6 decimals).
    """
    radius = int(radius or 0)
    base = DF.copy() if base_chain == "Todas" else DF[DF.cadeia == base_chain].copy()
    rows = []

    for _, r in base.iterrows():
        other = DF[DF.cadeia != r.cadeia].copy()
        if competitor_chain != "Todas":
            other = other[other.cadeia == competitor_chain]
        if other.empty:
            rows.append({**r.to_dict(), "dist_concorrente_m": np.nan, "concorrente_mais_proximo": "", "loja_concorrente": "", "morada_concorrente": "", "lat_concorrente": np.nan, "lon_concorrente": np.nan, "concorrentes_no_raio": 0})
            continue

        if radius <= 0:
            key = f"{float(r.latitude):.6f}|{float(r.longitude):.6f}"
            keys = other.apply(lambda x: f"{float(x.latitude):.6f}|{float(x.longitude):.6f}", axis=1)
            exact = other[keys == key]
            if exact.empty:
                rows.append({**r.to_dict(), "dist_concorrente_m": np.nan, "concorrente_mais_proximo": "", "loja_concorrente": "", "morada_concorrente": "", "lat_concorrente": np.nan, "lon_concorrente": np.nan, "concorrentes_no_raio": 0})
            else:
                rb = exact.iloc[0]
                rows.append({**r.to_dict(), "dist_concorrente_m": 0.0, "concorrente_mais_proximo": str(rb.cadeia), "loja_concorrente": str(rb.nome), "morada_concorrente": str(rb.morada), "lat_concorrente": float(rb.latitude), "lon_concorrente": float(rb.longitude), "concorrentes_no_raio": int(len(exact))})
        else:
            d = hdist_m(float(r.latitude), float(r.longitude), other.latitude.to_numpy(dtype=float), other.longitude.to_numpy(dtype=float))
            if len(d) == 0:
                rows.append({**r.to_dict(), "dist_concorrente_m": np.nan, "concorrente_mais_proximo": "", "loja_concorrente": "", "morada_concorrente": "", "lat_concorrente": np.nan, "lon_concorrente": np.nan, "concorrentes_no_raio": 0})
                continue
            j = int(np.argmin(d))
            rb = other.iloc[j]
            rows.append({**r.to_dict(), "dist_concorrente_m": float(d[j]), "concorrente_mais_proximo": str(rb.cadeia), "loja_concorrente": str(rb.nome), "morada_concorrente": str(rb.morada), "lat_concorrente": float(rb.latitude), "lon_concorrente": float(rb.longitude), "concorrentes_no_raio": int((d <= radius).sum())})

    out = pd.DataFrame(rows)
    text_cols = ["cadeia", "nome", "morada", "telefone", "email", "horario", "servicos", "concorrente_mais_proximo", "loja_concorrente"]
    for c in text_cols:
        if c in out.columns:
            out[c] = out[c].fillna("").astype(str)
    return out


def competition_map(df: pd.DataFrame, title: str):
    if df.empty:
        return empty_fig("Sem dados de concorrência")
    tmp = df.copy()
    tmp = tmp[tmp["concorrentes_no_raio"].fillna(0).astype(int) > 0].copy()
    if tmp.empty:
        return empty_fig("Nenhuma concorrência para os filtros selecionados")
    fig = go.Figure()
    line_lats, line_lons = [], []
    for row in tmp.itertuples(index=False):
        line_lats.extend([row.latitude, row.lat_concorrente, None])
        line_lons.extend([row.longitude, row.lon_concorrente, None])
    fig.add_trace(go.Scattermapbox(
        lat=line_lats, lon=line_lons, mode="lines",
        line={"width": 1.2, "color": "rgba(71,85,105,.38)"},
        hoverinfo="skip", name="Ligação ao mais próximo",
    ))
    base_points = tmp[["cadeia", "nome", "morada", "latitude", "longitude"]].copy()
    competitor_points = tmp[["concorrente_mais_proximo", "loja_concorrente", "morada_concorrente", "lat_concorrente", "lon_concorrente"]].copy()
    competitor_points.columns = ["cadeia", "nome", "morada", "latitude", "longitude"]
    competitor_points = competitor_points.drop_duplicates(["cadeia", "latitude", "longitude"])
    for role, points in (("Base", base_points), ("Concorrente", competitor_points)):
        for chain, sub in points.groupby("cadeia"):
            fig.add_trace(go.Scattermapbox(
                lat=sub.latitude, lon=sub.longitude, mode="markers",
                marker={"size": 14 if role == "Base" else 10, "color": CHAIN_COLORS.get(chain, "#111827"), "opacity": .88},
                text=sub.apply(lambda r: f"<b>{r.nome}</b><br>{role}: {chain}<br>{r.morada}", axis=1),
                hovertemplate="%{text}<extra></extra>", name=f"{chain} · {role}",
            ))
    all_lats = pd.concat([tmp.latitude, tmp.lat_concorrente]).dropna()
    all_lons = pd.concat([tmp.longitude, tmp.lon_concorrente]).dropna()
    fig.update_layout(
        mapbox_style="open-street-map", height=620, margin=dict(l=0, r=0, t=30, b=0),
        title=title, legend_title="Cadeia e papel",
        mapbox_center={"lat": float(all_lats.mean()), "lon": float(all_lons.mean())}, mapbox_zoom=5.2,
    )
    return add_spain_adm2_layer(fig)

DF_COMP = nearest_competition(DF)


def kpi_card(label, value):
    return dbc.Col(html.Div([html.Div(label, className="label"), html.Div(value, className="value")], className="kpi"), md=3)


def empty_fig(message="Sem dados"):
    fig = go.Figure()
    fig.add_annotation(text=message, x=0.5, y=0.5, showarrow=False, font=dict(size=18, color="#64748b"))
    fig.update_layout(template="plotly_white", height=520, margin=dict(l=20, r=20, t=20, b=20))
    return fig


def add_spain_adm2_layer(fig):
    """Overlay the locally cached geoBoundaries Spain ADM2 (provinces)."""
    if ESP_ADM2_GEOJSON:
        existing = list(fig.layout.mapbox.layers or [])
        existing.append({
            "sourcetype": "geojson",
            "source": ESP_ADM2_GEOJSON,
            "type": "line",
            "color": "rgba(30, 64, 175, 0.78)",
            "line": {"width": 1.35},
            "below": "traces",
        })
        fig.update_layout(mapbox_layers=existing)
    return fig


def map_fig(df: pd.DataFrame, title: str = "", color_by="cadeia", mode="Pontos"):
    if df.empty:
        return empty_fig("Sem lojas para apresentar")
    if mode == "Hexbin / Densidade":
        tmp = df.copy()
        tmp["lat_bin"] = (tmp.latitude / 0.12).round() * 0.12
        tmp["lon_bin"] = (tmp.longitude / 0.12).round() * 0.12
        agg = tmp.groupby(["lat_bin", "lon_bin"], as_index=False).size().rename(columns={"size": "lojas"})
        fig = px.scatter_mapbox(
            agg, lat="lat_bin", lon="lon_bin", size="lojas", color="lojas",
            color_continuous_scale="Viridis", size_max=32, zoom=5.2, height=620,
            hover_data={"lojas": True, "lat_bin": False, "lon_bin": False},
        )
    elif mode == "Distância ao concorrente":
        tmp = DF_COMP[DF_COMP.row_id.isin(df.row_id)].copy()
        tmp["dist_plot"] = tmp["dist_concorrente_m"].fillna(tmp["dist_concorrente_m"].max())
        fig = px.scatter_mapbox(
            tmp, lat="latitude", lon="longitude", color="dist_plot", size="concorrentes_no_raio",
            color_continuous_scale="RdYlGn", zoom=5.2, height=620,
            hover_name="nome",
            hover_data={"cadeia": True, "morada": True, "dist_concorrente_m": ":.0f", "concorrente_mais_proximo": True, "latitude": False, "longitude": False, "row_id": False, "dist_plot": False},
        )
    else:
        fig = px.scatter_mapbox(
            df, lat="latitude", lon="longitude", color=color_by,
            color_discrete_map=CHAIN_COLORS, zoom=5.2, height=620,
            hover_name="nome",
            hover_data={"cadeia": True, "morada": True, "telefone": True, "email": True, "latitude": ":.6f", "longitude": ":.6f", "row_id": False},
        )
    fig.update_layout(mapbox_style="open-street-map", margin=dict(l=0, r=0, t=30, b=0), title=title, legend_title="Cadeia")
    fig.update_traces(marker=dict(opacity=0.82))
    return add_spain_adm2_layer(fig)


def heatmap_fig(df: pd.DataFrame, title: str = ""):
    """Continuous density surface calculated from the store points."""
    if df.empty:
        return empty_fig("Sem lojas para apresentar")
    fig = px.density_mapbox(
        df,
        lat="latitude",
        lon="longitude",
        radius=18,
        zoom=5.0,
        height=620,
        color_continuous_scale=[
            [0.0, "rgba(37,99,235,0)"],
            [0.25, "#22c55e"],
            [0.55, "#facc15"],
            [0.8, "#f97316"],
            [1.0, "#dc2626"],
        ],
        hover_data={"latitude": ":.5f", "longitude": ":.5f"},
    )
    fig.update_layout(
        mapbox_style="open-street-map",
        margin=dict(l=0, r=0, t=30, b=0),
        title=title,
        coloraxis_colorbar_title="Densidade",
    )
    return add_spain_adm2_layer(fig)


def cluster_fig(df: pd.DataFrame, title: str = ""):
    """Client-side Mapbox clusters that expand as the user zooms in."""
    if df.empty:
        return empty_fig("Sem lojas para apresentar")
    fig = go.Figure()
    for cadeia, group in df.groupby("cadeia", sort=False):
        hover = group.apply(
            lambda r: f"<b>{r.nome}</b><br>{r.morada}<br>{r.municipio}<br>{r.latitude:.6f}, {r.longitude:.6f}",
            axis=1,
        )
        color = CHAIN_COLORS.get(str(cadeia), "#2563eb")
        fig.add_trace(go.Scattermapbox(
            lat=group.latitude,
            lon=group.longitude,
            mode="markers",
            marker={"size": 11, "color": color, "opacity": 0.82},
            cluster={"enabled": True, "maxzoom": 13, "step": 20, "size": 34, "color": color, "opacity": 0.82},
            text=hover,
            hovertemplate="%{text}<extra></extra>",
            name=str(cadeia),
        ))
    fig.update_layout(
        mapbox_style="open-street-map",
        mapbox_center={"lat": float(df.latitude.mean()), "lon": float(df.longitude.mean())},
        mapbox_zoom=5.0,
        height=620,
        margin=dict(l=0, r=0, t=30, b=0),
        title=title,
    )
    return add_spain_adm2_layer(fig)


def chain_table(df: pd.DataFrame):
    cols = ["nome", "cadeia", "morada", "municipio", "distrito", "telefone", "email", "horario", "servicos", "coords", "street_view", "apple_lookaround"]
    out = df[cols].copy()
    out["street_view"] = out["street_view"].apply(lambda u: f"[Street View]({u})")
    out["apple_lookaround"] = out["apple_lookaround"].apply(lambda u: f"[Apple Look Around]({u})")
    out = out.fillna("").replace("", "—")
    return dash_table.DataTable(
        data=out.to_dict("records"),
        columns=[
            {"name": "Loja", "id": "nome"}, {"name": "Cadeia", "id": "cadeia"}, {"name": "Morada", "id": "morada"},
            {"name": "Município", "id": "municipio"}, {"name": "Distrito", "id": "distrito"},
            {"name": "Telefone", "id": "telefone"}, {"name": "Email", "id": "email"}, {"name": "Horário", "id": "horario"},
            {"name": "Serviços", "id": "servicos"}, {"name": "Coordenadas", "id": "coords"},
            {"name": "Street View", "id": "street_view", "presentation": "markdown"},
            {"name": "Apple Look Around", "id": "apple_lookaround", "presentation": "markdown"},
        ],
        page_size=12,
        filter_action="native",
        sort_action="native",
        style_table={"overflowX": "auto"},
        style_cell={"fontFamily": "Inter, Segoe UI, Arial", "fontSize": 13, "padding": "9px", "textAlign": "left", "maxWidth": 320, "whiteSpace": "normal"},
        style_header={"fontWeight": "800", "backgroundColor": "#f8fafc"},
        markdown_options={"link_target": "_blank"},
    )


def intersection_table(df: pd.DataFrame):
    if df.empty:
        return html.Div("Nenhuma interseção encontrada para o raio selecionado.", className="cardx small-note")
    out = df[["cadeia_a", "loja_a", "lat_a", "lon_a", "municipio_a", "distrito_a", "cadeia_b", "loja_b", "lat_b", "lon_b", "municipio_b", "distrito_b", "dist_m", "street_view_a", "apple_lookaround_a", "street_view_b", "apple_lookaround_b"]].copy()
    out["ponto_a"] = out.apply(lambda r: f"{r.lat_a:.6f}, {r.lon_a:.6f}", axis=1)
    out["ponto_b"] = out.apply(lambda r: f"{r.lat_b:.6f}, {r.lon_b:.6f}", axis=1)
    out["dist_m"] = out["dist_m"].round(1)
    for c in ["street_view_a", "street_view_b"]:
        out[c] = out[c].apply(lambda u: f"[Street View]({u})")
    for c in ["apple_lookaround_a", "apple_lookaround_b"]:
        out[c] = out[c].apply(lambda u: f"[Apple Look Around]({u})")
    return dash_table.DataTable(
        data=out.to_dict("records"),
        columns=[
            {"name": "Cadeia A", "id": "cadeia_a"}, {"name": "Loja A", "id": "loja_a"},
            {"name": "Ponto A", "id": "ponto_a"},
            {"name": "Cadeia B", "id": "cadeia_b"}, {"name": "Loja B", "id": "loja_b"},
            {"name": "Ponto B", "id": "ponto_b"},
            {"name": "Distância (m)", "id": "dist_m", "type": "numeric"},
            {"name": "Município A", "id": "municipio_a"}, {"name": "Distrito A", "id": "distrito_a"},
            {"name": "Município B", "id": "municipio_b"}, {"name": "Distrito B", "id": "distrito_b"},
            {"name": "Street View A", "id": "street_view_a", "presentation": "markdown"},
            {"name": "Look Around A", "id": "apple_lookaround_a", "presentation": "markdown"},
            {"name": "Street View B", "id": "street_view_b", "presentation": "markdown"},
            {"name": "Look Around B", "id": "apple_lookaround_b", "presentation": "markdown"},
        ],
        page_size=12,
        filter_action="native",
        sort_action="native",
        style_table={"overflowX": "auto", "minWidth": "100%"},
        style_cell={"fontFamily": "Inter, Segoe UI, Arial", "fontSize": 13, "padding": "9px", "textAlign": "left", "maxWidth": 280, "whiteSpace": "normal"},
        style_header={"fontWeight": "800", "backgroundColor": "#f8fafc"},
        markdown_options={"link_target": "_blank"},
    )


def inter_map(df: pd.DataFrame):
    if df.empty:
        return empty_fig("Sem interseções para o raio selecionado")
    fig = go.Figure()
    # Lines limited for performance
    for _, r in df.head(700).iterrows():
        fig.add_trace(go.Scattermapbox(
            lat=[r.lat_a, r.lat_b], lon=[r.lon_a, r.lon_b], mode="lines",
            line=dict(width=1, color="rgba(124,58,237,.35)"), hoverinfo="skip", showlegend=False
        ))
    pts_a = df[["cadeia_a", "loja_a", "lat_a", "lon_a"]].rename(columns={"cadeia_a": "cadeia", "loja_a": "loja", "lat_a": "lat", "lon_a": "lon"})
    pts_b = df[["cadeia_b", "loja_b", "lat_b", "lon_b"]].rename(columns={"cadeia_b": "cadeia", "loja_b": "loja", "lat_b": "lat", "lon_b": "lon"})
    pts = pd.concat([pts_a, pts_b], ignore_index=True).drop_duplicates()
    for cadeia, sub in pts.groupby("cadeia"):
        fig.add_trace(go.Scattermapbox(
            lat=sub.lat, lon=sub.lon, mode="markers", name=cadeia,
            marker=dict(size=10, color=CHAIN_COLORS.get(cadeia, "#111827"), opacity=.9),
            text=sub.loja, hovertemplate="<b>%{text}</b><br>" + cadeia + "<extra></extra>"
        ))
    fig.update_layout(mapbox_style="open-street-map", height=620, margin=dict(l=0, r=0, t=20, b=0), legend_title="Cadeia")
    fig.update_mapboxes(center=dict(lat=float(pts.lat.mean()), lon=float(pts.lon.mean())), zoom=6)
    return add_spain_adm2_layer(fig)


def intersection_heatmap(df: pd.DataFrame):
    """Density of competitive pressure, weighted by intersection relationships."""
    if df.empty:
        return empty_fig("Sem interseções para o heatmap")
    pts_a = df[["cadeia_a", "loja_a", "lat_a", "lon_a"]].rename(
        columns={"cadeia_a": "cadeia", "loja_a": "loja", "lat_a": "lat", "lon_a": "lon"}
    )
    pts_b = df[["cadeia_b", "loja_b", "lat_b", "lon_b"]].rename(
        columns={"cadeia_b": "cadeia", "loja_b": "loja", "lat_b": "lat", "lon_b": "lon"}
    )
    pressure = pd.concat([pts_a, pts_b], ignore_index=True)
    pressure = pressure.groupby(["cadeia", "loja", "lat", "lon"], as_index=False).size().rename(columns={"size": "intersecoes"})
    fig = px.density_mapbox(
        pressure, lat="lat", lon="lon", z="intersecoes", radius=24,
        color_continuous_scale=[
            [0.0, "rgba(37,99,235,0)"], [0.25, "#22c55e"],
            [0.55, "#facc15"], [0.8, "#f97316"], [1.0, "#dc2626"],
        ],
        hover_name="loja", hover_data={"cadeia": True, "intersecoes": True, "lat": False, "lon": False},
        zoom=5.2, height=620,
    )
    fig.update_layout(
        mapbox_style="open-street-map", margin=dict(l=0, r=0, t=30, b=0),
        title="Pressão concorrencial", coloraxis_colorbar_title="Interseções",
        mapbox_center={"lat": float(pressure.lat.mean()), "lon": float(pressure.lon.mean())},
    )
    return add_spain_adm2_layer(fig)


def sidebar():
    chain_links = [dcc.Link(f"🏪 {c}", href=f"/cadeia/{c}", className="side-link") for c in CHAINS]
    return html.Div([
        html.H2("GIS Geomarketing"),
        dcc.Link("🏠 Dashboard", href="/", className="side-link"),
        html.Div("Cadeias", className="side-section"),
        *chain_links,
        html.Div("Análise espacial", className="side-section"),
        dcc.Link("📍 Interseções", href="/intersecoes", className="side-link"),
        dcc.Link("🔢 Matriz", href="/matriz", className="side-link"),
        dcc.Link("🟠 Clusters", href="/clusters", className="side-link"),
        dcc.Link("⬢ Hexbin / Densidade", href="/densidade", className="side-link"),
        dcc.Link("🎯 Concorrência", href="/concorrencia", className="side-link"),
        dcc.Link("📊 Estatísticas", href="/estatisticas", className="side-link"),
        dcc.Link("♻️ Candidatos Volta", href="/candidatos-volta", className="side-link"),
        dcc.Link("📰 News", href="/news", className="side-link"),
        dcc.Link("✅ Qualidade dos dados", href="/qualidade", className="side-link"),
        html.Div("Downloads", className="side-section"),
        html.Button("CSV", id="download-csv-btn", className="btn btn-sm btn-light me-2"),
        html.Button("Excel", id="download-xlsx-btn", className="btn btn-sm btn-outline-light"),
        dcc.Download(id="download-csv"), dcc.Download(id="download-xlsx"),
        dbc.Button("⬇ Download Interseções CSV", id="download-intersections-btn", color="success", className="w-100 mt-2"),
        dcc.Download(id="download-intersections"),
    ], className="sidebar")


def page_dashboard():
    counts = DF.groupby("cadeia").size().reset_index(name="lojas")
    fig_bar = px.bar(counts, x="cadeia", y="lojas", color="cadeia", color_discrete_map=CHAIN_COLORS, text="lojas", height=620)
    fig_bar.update_layout(showlegend=False, margin=dict(l=20, r=20, t=20, b=20), template="plotly_white")
    return html.Div([
        html.H1("Plataforma GIS de Geomarketing", className="page-title"),
        html.P("Distribuição, concorrência, interseções e análise espacial de redes de retalho.", className="subtitle"),
        dbc.Row([
            kpi_card("Total de lojas", f"{len(DF):,}".replace(",", ".")),
            kpi_card("Cadeias", len(CHAINS)),
            kpi_card("Com telefone", int((DF.telefone != "").sum())),
            kpi_card("Com email", int((DF.email != "").sum())),
        ], className="g-3 mb-4"),
        dbc.Row([
            dbc.Col(html.Div(dcc.Graph(figure=map_fig(DF, "Mapa geral", "cadeia", "Pontos"), responsive=True), className="cardx"), lg=8, md=12),
            dbc.Col(html.Div(dcc.Graph(figure=fig_bar, responsive=True), className="cardx"), lg=4, md=12),
        ], className="g-3"),
    ])


def page_chain(cadeia: str):
    df = DF[DF.cadeia == cadeia].copy()
    return html.Div([
        html.H1(cadeia, className="page-title"),
        html.P("Pontos, densidade e clusters da cadeia selecionada.", className="subtitle"),
        dbc.Row([
            kpi_card("Lojas", len(df)),
            kpi_card("Com telefone", int((df.telefone != "").sum())),
            kpi_card("Com email", int((df.email != "").sum())),
            kpi_card("Municípios", int(df.municipio.replace('', np.nan).nunique())),
        ], className="g-3 mb-4"),
        html.Div(
            [
                dcc.Store(id="chain-current", data=cadeia),
                dbc.Tabs(
                    [
                        dbc.Tab(label="Mapa e pontos", tab_id="points"),
                        dbc.Tab(label="Heatmap", tab_id="heatmap"),
                        dbc.Tab(label="Clusters", tab_id="clusters"),
                    ],
                    id="chain-view-tabs",
                    active_tab="points",
                    className="chain-tabs",
                ),
                dcc.Loading(
                    dcc.Graph(id="chain-view-graph", responsive=True, style={"width": "100%", "height": "68vh", "minHeight": "620px"}),
                    type="circle",
                ),
            ],
            className="cardx mb-4",
        ),
        html.Div(chain_table(df), className="cardx"),
    ])


def page_intersections():
    pair_opts = PAIR_OPTIONS
    default_pair = pair_opts[1] if len(pair_opts) > 1 else "Todas"
    return html.Div([
        html.H1("Interseções", className="page-title"),
        html.P("Identifica exatamente quais lojas ficam próximas entre redes. Sem heatmap borrado.", className="subtitle"),
        html.Div([
            dbc.Row([
                dbc.Col([html.Label("Par de cadeias", className="fw-bold"), dcc.Dropdown(pair_opts, default_pair, id="inter-pair", clearable=False)], md=3),
                dbc.Col([html.Label("Raio de interseção (m)", className="fw-bold"), dcc.Slider(0, 2000, value=500, marks={0:"0",50:"50",250:"250",500:"500",1000:"1 km",2000:"2 km"}, id="inter-radius")], md=7),
                dbc.Col([html.Label(" "), dbc.Input(id="inter-radius-input", value=500, type="number", min=0, max=5000)], md=2),
            ])
        ], className="cardx mb-4"),
        html.Div(id="inter-kpis", className="mb-4"),
        dbc.Row([
            dbc.Col(html.Div(dcc.Graph(id="inter-map", responsive=True), className="cardx"), lg=6, md=12),
            dbc.Col(html.Div(dcc.Graph(id="inter-heatmap", responsive=True), className="cardx"), lg=6, md=12),
        ], className="g-3 mb-4 intersection-maps"),
        html.Div(id="inter-table-wrap", className="cardx table-card"),
    ])


def page_matrix():
    return html.Div([
        html.H1("Matriz de interseções", className="page-title"),
        html.P("Número de pares de lojas por cadeia dentro do raio selecionado.", className="subtitle"),
        html.Div([html.Label("Raio (m)", className="fw-bold"), dcc.Slider(0, 2000, value=500, marks={0:"0",50:"50",250:"250",500:"500",1000:"1 km",2000:"2 km"}, id="matrix-radius")], className="cardx mb-4"),
        html.Div(id="matrix-table", className="cardx"),
    ])


def page_density():
    return html.Div([
        html.H1("Hexbin / Densidade", className="page-title"),
        html.P("Mapa de densidade legível. Substitui o heatmap saturado.", className="subtitle"),
        html.Div(dcc.Graph(figure=map_fig(DF, "Densidade por células", mode="Hexbin / Densidade")), className="cardx"),
    ])


def page_clusters():
    return html.Div([
        html.H1("Clusters de lojas", className="page-title"),
        html.P(
            "Aglomerações comerciais interativas por cadeia. Aumente o zoom para expandir cada cluster e ver as lojas.",
            className="subtitle",
        ),
        dbc.Row([
            kpi_card("Lojas agrupáveis", f"{len(DF):,}".replace(",", ".")),
            kpi_card("Cadeias", len(CHAINS)),
            kpi_card("Zoom de expansão", "até 13"),
            kpi_card("Passo do cluster", "20 pontos"),
        ], className="g-3 mb-4"),
        html.Div(
            dcc.Graph(figure=cluster_fig(DF, "Clusters comerciais por cadeia"), responsive=True),
            className="cardx",
        ),
        html.P(
            "Os círculos representam concentrações de lojas, não limites oficiais de aglomerações urbanas.",
            className="small-note mt-2",
        ),
    ])


def page_data_quality():
    report = pd.DataFrame(DATA_QUALITY_REPORT)
    report = report[report["registos"] > 0].copy() if not report.empty else report
    return html.Div([
        html.H1("Qualidade dos dados", className="page-title"),
        html.P("Registos excluídos ou sinalizados durante o carregamento dos datasets.", className="subtitle"),
        html.Div(
            dash_table.DataTable(
                data=report.to_dict("records"),
                columns=[{"name": c.replace("_", " ").title(), "id": c} for c in report.columns],
                sort_action="native",
                page_size=20,
                style_cell={"padding": "12px", "textAlign": "left"},
                style_header={"fontWeight": "800", "backgroundColor": "#f8fafc"},
            ) if not report.empty else dbc.Alert("Nenhuma anomalia detetada.", color="success"),
            className="cardx",
        ),
    ])


def page_competition():
    chain_opts = ["Todas"] + CHAINS
    return html.Div([
        html.H1("Concorrência", className="page-title"),
        html.P("Analisa concorrentes próximos. Raio 0 m = mesmo ponto/coordenada exata.", className="subtitle"),
        html.Div([
            dbc.Row([
                dbc.Col([html.Label("Cadeia base", className="fw-bold"), dcc.Dropdown(chain_opts, "Todas", id="comp-base", clearable=False)], md=3),
                dbc.Col([html.Label("Concorrente", className="fw-bold"), dcc.Dropdown(chain_opts, "Todas", id="comp-target", clearable=False)], md=3),
                dbc.Col([html.Label("Raio (m)", className="fw-bold"), dcc.Slider(0, 2000, value=500, marks={0:"0",50:"50",250:"250",500:"500",1000:"1 km",2000:"2 km"}, id="comp-radius")], md=6),
            ])
        ], className="cardx mb-4"),
        html.Div(id="comp-kpis", className="mb-4"),
        html.Div(dcc.Graph(id="comp-map"), className="cardx mb-4"),
        html.Div(id="comp-table-wrap", className="cardx"),
    ])


def page_statistics():
    chain_opts = ["Todas"] + CHAINS
    return html.Div([
        html.H1("Estatísticas por Cadeia", className="page-title"),
        html.P("Comparativo detalhado entre cadeias, municípios e distritos.", className="subtitle"),

        # Filtros
        html.Div([
            dbc.Row([
                dbc.Col([html.Label("Cadeia", className="fw-bold"), dcc.Dropdown(chain_opts, "Todas", id="stat-chain", clearable=False)], md=3),
            ])
        ], className="cardx mb-4"),

        # KPIs
        html.Div(id="stat-kpis", className="mb-4"),

        # Gráficos
        dbc.Row([
            dbc.Col([dcc.Graph(id="stat-bar-chain")], md=6),
            dbc.Col([dcc.Graph(id="stat-bar-municipality")], md=6),
        ], className="g-3 mb-3"),

        dbc.Row([
            dbc.Col([dcc.Graph(id="stat-bar-district")], md=12),
        ], className="g-3 mb-3"),

        dbc.Row([
            dbc.Col([dcc.Graph(id="stat-pie-chain")], md=6),
            dbc.Col([html.Div(id="stat-table-chain", className="cardx h-100")], md=6),
        ], className="g-3"),
    ])


def page_news():
    return html.Div([
        html.H1("Destacado en Alimentación", className="page-title news-heading"),
        html.P("Atualizações públicas sobre distribuição alimentar. Os artigos abrem sempre na fonte original.", className="subtitle"),
        html.Div([
            dbc.Button("↻ Atualizar agora", id="news-refresh", color="success", size="sm"),
            html.Span(id="news-updated-at", className="news-updated-at"),
        ], className="news-toolbar"),
        dcc.Interval(id="news-interval", interval=15 * 60 * 1000, n_intervals=0),
        html.Div(id="news-content"),
    ])


def page_volta_candidates():
    return html.Div([
        html.H1([
            "Diretiva ",
            html.A(
                "INSPIRE",
                href="https://www.catastro.hacienda.gob.es/webinspire/index.html",
                target="_blank",
                rel="noopener noreferrer",
                className="inspire-title-link",
            ),
            " 2007/2/CE",
        ], className="page-title"),
        html.P(
            "Triagem espacial de supermercados pelo edifício cadastral. A área apresentada é a implantação do edifício, não a área de venda confirmada.",
            className="subtitle",
        ),
        html.Div([
            dbc.Row([
                dbc.Col([html.Label("Cadeia", className="fw-bold"), dcc.Dropdown(["Todas"] + CHAINS, None, id="volta-chain", placeholder="Escolha uma cadeia", clearable=True)], md=4),
                dbc.Col([html.Label("Classificação", className="fw-bold"), dcc.Dropdown(
                    ["Todos", "Provável", "Improvável", "Verificar", "Centro comercial"],
                    None, id="volta-status", placeholder="Escolha uma classificação", clearable=True,
                )], md=4),
                dbc.Col([html.Label("Área mínima do edifício (m²)", className="fw-bold"), dbc.Input(id="volta-min-area", type="number", value=0, min=0)], md=4),
            ], className="g-3")
        ], className="cardx mb-4"),
        html.Div(id="volta-kpis", className="mb-4"),
        dbc.Row([
            dbc.Col(
                html.Div(
                    dcc.Graph(
                        id="volta-map",
                        responsive=True,
                        config={"responsive": True},
                        style={"width": "100%", "height": "610px", "minHeight": "610px"},
                    ),
                    className="cardx volta-map-card",
                ),
                id="volta-map-col", lg=7, md=12,
            ),
            dbc.Col(html.Div([
                html.H4("Critérios de triagem"),
                html.Ul([
                    html.Li("Provável: 400–5.000 m² e loja isolada"),
                    html.Li("Improvável: edifício abaixo de 400 m²"),
                    html.Li("Centro comercial: acima de 5.000 m² ou complexo multioperador"),
                    html.Li("Verificar: área cadastral ainda desconhecida ou situação ambígua"),
                ]),
                dbc.Alert("A elegibilidade final exige a área de venda confirmada.", color="warning"),
            ], className="cardx h-100"), id="volta-criteria", lg=5, md=12),
        ], className="g-3 mb-4"),
        html.Div(id="volta-table", className="cardx table-card"),
    ])


def render_news_content(news: list[dict]):
    cards = [
        html.Div([
            html.A(item["title"], href=item["link"], target="_blank", rel="noopener noreferrer", className="news-title"),
        ], className="news-card")
        for item in news
    ]
    if not cards:
        cards = [dbc.Alert(
            "O feed de notícias está temporariamente indisponível. Use os links abaixo para consultar as fontes.",
            color="warning",
        )]
    return html.Div([
        html.Div([
            html.Span("Relatório permanente", className="news-report-label"),
            html.A(
                "Informe 2026 sobre la Distribución Alimentaria en España por superficie ↗",
                href=ALIMARKET_REPORT,
                target="_blank",
                rel="noopener noreferrer",
                className="news-report-link",
            ),
        ], className="news-report"),
        html.Div(cards, className="news-grid"),
        html.P("Fonte: página pública Alimentación, Alimarket. Clique numa manchete para abrir o artigo original.", className="small-note"),
    ])


app = Dash(__name__, external_stylesheets=[dbc.themes.BOOTSTRAP], suppress_callback_exceptions=True)
server = app.server
app.layout = html.Div([dcc.Location(id="url"), sidebar(), html.Main(id="page", className="main")])


@app.callback(
    Output("chain-view-graph", "figure"),
    Input("chain-view-tabs", "active_tab"),
    State("chain-current", "data"),
)
def update_chain_map(active_tab, cadeia):
    df = DF[DF.cadeia == cadeia].copy()
    if active_tab == "heatmap":
        return heatmap_fig(df, f"Heatmap - {cadeia}")
    if active_tab == "clusters":
        return cluster_fig(df, f"Clusters - {cadeia}")
    return map_fig(df, f"Pontos - {cadeia}")


@app.callback(
    Output("news-content", "children"),
    Output("news-updated-at", "children"),
    Input("news-interval", "n_intervals"),
    Input("news-refresh", "n_clicks"),
)
def refresh_market_news(_intervals, _clicks):
    news = load_featured_food_news() or load_market_news(limit=9)
    timestamp = datetime.now().strftime("Atualizado em %d/%m/%Y às %H:%M")
    return render_news_content(news), timestamp


@app.callback(Output("page", "children"), Input("url", "pathname"))
def router(pathname):
    try:
        if not pathname or pathname == "/":
            return page_dashboard()
        if pathname.startswith("/cadeia/"):
            cadeia = pathname.split("/cadeia/", 1)[1].replace("%20", " ")
            return page_chain(cadeia if cadeia in CHAINS else CHAINS[0])
        if pathname == "/intersecoes":
            return page_intersections()
        if pathname == "/matriz":
            return page_matrix()
        if pathname == "/clusters":
            return page_clusters()
        if pathname == "/densidade":
            return page_density()
        if pathname == "/concorrencia":
            return page_competition()
        if pathname == "/estatisticas":
            return page_statistics()
        if pathname == "/candidatos-volta":
            return page_volta_candidates()
        if pathname == "/news":
            return page_news()
        if pathname == "/qualidade":
            return page_data_quality()
        return page_dashboard()
    except Exception as e:
        return html.Div([html.H1("Erro"), html.Pre(str(e))], className="main")


@app.callback(Output("inter-radius-input", "value"), Input("inter-radius", "value"))
def sync_radius(v):
    return v


@app.callback(
    Output("volta-kpis", "children"),
    Output("volta-map", "figure"),
    Output("volta-table", "children"),
    Output("volta-kpis", "style"),
    Output("volta-map-col", "style"),
    Output("volta-criteria", "style"),
    Output("volta-table", "style"),
    Input("volta-chain", "value"),
    Input("volta-status", "value"),
    Input("volta-min-area", "value"),
)
def update_volta_candidates(chain, status, min_area):
    chain_is_all = not chain or chain == "Todas"
    status_is_all = not status or status == "Todos"
    initial_view = chain_is_all and status_is_all
    if initial_view:
        fig = go.Figure(go.Scattermapbox(lat=[], lon=[]))
        fig.update_layout(
            mapbox_style="open-street-map",
            mapbox_center={"lat": 40.2, "lon": -3.7},
            mapbox_zoom=5,
            height=610,
            margin=dict(l=0, r=0, t=0, b=0),
            showlegend=False,
        )
        fig = add_spain_adm2_layer(fig)
        return [], fig, [], {"display": "none"}, {"width": "100%", "flex": "0 0 100%", "maxWidth": "100%"}, {"display": "none"}, {"display": "none"}

    df = volta_candidates()
    if chain and chain != "Todas":
        df = df[df["cadeia"] == chain]
    if status and status != "Todos":
        df = df[df["status_volta"] == status]
    min_area = float(min_area or 0)
    if min_area > 0:
        researched = df["area_edificio_m2"].notna()
        df = df[(~researched) | (df["area_edificio_m2"] >= min_area)]

    researched_count = int(df["area_edificio_m2"].notna().sum())
    verify_count = int((df["status_volta"] == "Verificar").sum())
    eligible_count = int((df["status_volta"] == "Provável").sum())
    mall_count = int((df["status_volta"] == "Centro comercial").sum())
    kpis = dbc.Row([
        kpi_card("Lojas apresentadas", len(df)),
        kpi_card("Com Catastro", researched_count),
        kpi_card("Prováveis candidatas", eligible_count),
        kpi_card("Verificar / centros", verify_count + mall_count),
    ], className="g-3")

    colors = {"Provável": "#16a34a", "Verificar": "#f59e0b", "Improvável": "#dc2626", "Centro comercial": "#7c3aed"}
    fig = px.scatter_mapbox(
        df, lat="latitude", lon="longitude", color="status_volta", color_discrete_map=colors,
        hover_name="nome", hover_data={"cadeia": True, "morada": True, "area_edificio_m2": ":.1f", "contexto": True, "latitude": False, "longitude": False},
        zoom=5, height=610,
    ) if not df.empty else empty_fig("Nenhum candidato com estes filtros")
    if not df.empty:
        fig.update_layout(mapbox_style="open-street-map", margin=dict(l=0, r=0, t=20, b=0), legend_title="Classificação")
        fig = add_spain_adm2_layer(fig)

    display = df.copy()
    display["area_edificio_m2"] = display["area_edificio_m2"].round(1)
    table_columns = ["cadeia", "nome", "morada", "municipio", "area_edificio_m2", "contexto", "status_volta", "motivo", "referencia_cadastral"]
    table = dash_table.DataTable(
        data=display[table_columns].to_dict("records"),
        columns=[{"name": c.replace("_", " ").title(), "id": c} for c in table_columns],
        sort_action="native", filter_action="native", page_size=15,
        style_table={"overflowX": "auto"},
        style_cell={"padding": "10px", "textAlign": "left", "minWidth": "120px", "maxWidth": "280px", "whiteSpace": "normal"},
        style_header={"fontWeight": "800", "backgroundColor": "#f8fafc"},
        style_data_conditional=[
            {"if": {"filter_query": '{status_volta} = "Provável"', "column_id": "status_volta"}, "color": "#15803d", "fontWeight": "700"},
            {"if": {"filter_query": '{status_volta} = "Verificar"', "column_id": "status_volta"}, "color": "#c2410c", "fontWeight": "700"},
            {"if": {"filter_query": '{status_volta} = "Improvável"', "column_id": "status_volta"}, "color": "#b91c1c", "fontWeight": "700"},
            {"if": {"filter_query": '{status_volta} = "Centro comercial"', "column_id": "status_volta"}, "color": "#6d28d9", "fontWeight": "700"},
        ],
    )
    return kpis, fig, table, {}, {}, {}, {}


@app.callback(
    Output("inter-kpis", "children"),
    Output("inter-map", "figure"),
    Output("inter-heatmap", "figure"),
    Output("inter-table-wrap", "children"),
    Input("inter-pair", "value"),
    Input("inter-radius", "value"),
)
def update_intersections(pair_value, radius):
    try:
        radius = int(radius or DEFAULT_RADIUS)
        inter = all_intersections(radius, pair_value or "Todas")
        # Store names repeat across a chain (for example, many rows are simply
        # called "Dia"). Coordinates identify the physical locations reliably.
        unique_a = inter[["cadeia_a", "lat_a", "lon_a"]].drop_duplicates().shape[0] if not inter.empty else 0
        unique_b = inter[["cadeia_b", "lat_b", "lon_b"]].drop_duplicates().shape[0] if not inter.empty else 0
        label_a = f"Lojas {inter.iloc[0].cadeia_a}" if not inter.empty else "Lojas lado A"
        label_b = f"Lojas {inter.iloc[0].cadeia_b}" if not inter.empty else "Lojas lado B"
        avg = f"{inter.dist_m.mean():.0f} m" if not inter.empty else "—"
        kpis = dbc.Row([
            kpi_card("Pares encontrados", len(inter)),
            kpi_card(label_a, unique_a),
            kpi_card(label_b, unique_b),
            kpi_card("Distância média", avg),
        ], className="g-3")
        return kpis, inter_map(inter), intersection_heatmap(inter), intersection_table(inter)
    except Exception as e:
        kpis = dbc.Alert(f"Erro no cálculo: {e}", color="danger")
        return kpis, empty_fig("Erro ao calcular interseções"), empty_fig("Erro no heatmap"), html.Div(str(e), className="small-note")


@app.callback(Output("matrix-table", "children"), Input("matrix-radius", "value"))
def update_matrix(radius):
    try:
        radius=int(radius or DEFAULT_RADIUS)
        rows=[]
        totals={c: len(DF[DF["cadeia"]==c]) for c in CHAINS}
        for a,b in ALLOWED_INTERSECTION_PAIRS:
            inter=intersection_pairs(a,b,radius,max_rows=100000)
            if inter.empty:
                ua=ub=0
            else:
                ua=inter["row_id_a"].nunique() if "row_id_a" in inter.columns else inter[["cadeia_a","loja_a","morada_a"]].drop_duplicates().shape[0]
                ub=inter["row_id_b"].nunique() if "row_id_b" in inter.columns else inter[["cadeia_b","loja_b","morada_b"]].drop_duplicates().shape[0]
            rows.append({
                "Cadeia A":a,
                "Cadeia B":b,
                "Lojas Cadeia A":ua,
                "Lojas Cadeia B":ub,
                "% Cadeia A":f"{ua/totals[a]*100:.1f}%" if totals[a] else "0%",
                "% Cadeia B":f"{ub/totals[b]*100:.1f}%" if totals[b] else "0%",
            })
        return dash_table.DataTable(
            data=rows,
            columns=[{"name":c,"id":c} for c in rows[0].keys()],
            style_cell={"padding":"12px","textAlign":"center","fontFamily":"Inter, Segoe UI, Arial"},
            style_header={"fontWeight":"800","backgroundColor":"#f8fafc"},
        )
    except Exception as e:
        return dbc.Alert(str(e), color="danger")



@app.callback(
    Output("comp-kpis", "children"),
    Output("comp-map", "figure"),
    Output("comp-table-wrap", "children"),
    Input("comp-base", "value"),
    Input("comp-target", "value"),
    Input("comp-radius", "value"),
)
def update_competition(base_chain, competitor_chain, radius):
    try:
        radius = int(radius or 0)
        comp = competition_dataset(base_chain or "Todas", competitor_chain or "Todas", radius)
        hits = comp[comp["concorrentes_no_raio"].fillna(0).astype(int) > 0].copy()
        avg = f"{hits.dist_concorrente_m.mean():.1f} m" if not hits.empty else "—"
        mode_label = "Mesmo ponto" if radius <= 0 else f"≤ {radius} m"
        kpis = dbc.Row([
            kpi_card("Filtro", mode_label),
            kpi_card("Lojas com concorrência", len(hits)),
            kpi_card("Distância média", avg),
            kpi_card("Máx. concorrentes", int(hits.concorrentes_no_raio.max()) if not hits.empty else 0),
        ], className="g-3")
        table = chain_table(hits.sort_values(["concorrentes_no_raio", "dist_concorrente_m"], ascending=[False, True]).head(1000)) if not hits.empty else html.Div("Nenhuma loja com concorrência para os filtros selecionados.", className="small-note")
        return kpis, competition_map(comp, "Concorrência"), table
    except Exception as e:
        return dbc.Alert(f"Erro no cálculo de concorrência: {e}", color="danger"), empty_fig("Erro"), html.Div(str(e), className="small-note")


@app.callback(Output("download-csv", "data"), Input("download-csv-btn", "n_clicks"), prevent_initial_call=True)
def dl_csv(n):
    # Gerar dados de concorrência (inclui as colunas dist_concorrente_m, concorrentes_no_raio, etc.)
    df_combined = competition_dataset("Todas", "Todas", DEFAULT_RADIUS)

    # Garantir tipo correcto na coluna de distância
    if "dist_concorrente_m" in df_combined.columns:
        df_combined["dist_concorrente_m"] = pd.to_numeric(df_combined["dist_concorrente_m"], errors="coerce")

    # Garantir tipo correcto na coluna de contagem de concorrentes
    if "concorrentes_no_raio" in df_combined.columns:
        df_combined["concorrentes_no_raio"] = pd.to_numeric(df_combined["concorrentes_no_raio"], errors="coerce")

    # Agregar por cadeia — as colunas já existem neste ponto
    chain_aggregation = df_combined.groupby("cadeia").agg(
        total_lojas=("nome", "count"),
        media_distancia=("dist_concorrente_m", "mean"),
        max_concorrentes=("concorrentes_no_raio", "max"),
        lojas_com_concorrente=("dist_concorrente_m", lambda x: x.notna().sum())
    ).reset_index()

    # Renomear colunas para maior clareza
    chain_aggregation.columns = [
        "Cadeia",
        "Total de Lojas",
        "Distância Média (m)",
        "Máx. Concorrentes",
        "Lojas com Concorrência"
    ]

    # Substituir valores vazios nas colunas de texto de concorrência
    for col in ["concorrente_mais_proximo", "loja_concorrente"]:
        if col in df_combined.columns:
            df_combined[col] = df_combined[col].replace("", "Nenhum")

    # Exportar apenas o DataFrame principal (com colunas de concorrência já incluídas)
    return dcc.send_data_frame(df_combined.to_csv, "geomarketing_dados_completo.csv", index=False, encoding="utf-8-sig")


@app.callback(Output("download-xlsx", "data"), Input("download-xlsx-btn", "n_clicks"), prevent_initial_call=True)
def dl_xlsx(n):
    buf = io.BytesIO()
    with pd.ExcelWriter(buf, engine="openpyxl") as writer:
        DF.to_excel(writer, index=False, sheet_name="lojas")
        DF_COMP.to_excel(writer, index=False, sheet_name="concorrencia")
    buf.seek(0)
    return dcc.send_bytes(buf.getvalue(), "geomarketing_dados.xlsx")


# Callbacks de Estatísticas
@app.callback(
    [
        Output("stat-kpis", "children"),
        Output("stat-bar-chain", "figure"),
        Output("stat-bar-municipality", "figure"),
        Output("stat-bar-district", "figure"),
        Output("stat-pie-chain", "figure"),
        Output("stat-table-chain", "children"),
    ],
    Input("stat-chain", "value"),
)
def update_statistics(chain_filter):
    try:
        df = DF.copy()

        # Filtrar por cadeia
        if chain_filter != "Todas":
            df = df[df["cadeia"] == chain_filter]

        # KPIs
        kpis = dbc.Row([
            kpi_card("Total de lojas", len(df)),
            kpi_card("Cadeia selecionada", chain_filter),
        ], className="g-3")

        # Gráfico de barras - Quantidade por cadeia (se filtro de cadeia)
        if chain_filter == "Todas":
            # Mostrar todas as cadeias
            chain_counts = df.groupby("cadeia").size().sort_values(ascending=False)
            fig_bar_chain = go.Figure([
                go.Bar(x=chain_counts.index, y=chain_counts.values, text=chain_counts.values, textposition="auto")
            ])
            fig_bar_chain.update_layout(
                title="Quantidade de lojas por cadeia",
                xaxis_title="Cadeia de supermercado",
                yaxis_title="Número de lojas",
                height=400,
                showlegend=False
            )
        else:
            # Para uma cadeia, mostrar a qualidade/completude dos campos principais.
            fields = {
                "Morada": "morada",
                "Município": "municipio",
                "Distrito": "distrito",
                "Telefone": "telefone",
                "Email": "email",
            }
            coverage = []
            for label, column in fields.items():
                values = df[column].fillna("").astype(str).str.strip()
                coverage.append({"campo": label, "percentagem": round((values != "").mean() * 100, 1) if len(df) else 0})
            coverage_df = pd.DataFrame(coverage)
            fig_bar_chain = px.bar(
                coverage_df,
                x="campo",
                y="percentagem",
                text="percentagem",
                range_y=[0, 100],
                title=f"Completude dos dados — {chain_filter}",
                labels={"campo": "Campo", "percentagem": "Registos preenchidos (%)"},
                height=400,
            )
            fig_bar_chain.update_traces(texttemplate="%{text:.1f}%", textposition="outside", marker_color=CHAIN_COLORS.get(chain_filter, "#2563eb"))
            fig_bar_chain.update_layout(showlegend=False)

        # Gráfico de barras - Quantidade por município
        muni_counts = df.groupby("municipio").size().sort_values(ascending=False).head(15)
        fig_bar_muni = go.Figure([
            go.Bar(x=muni_counts.index, y=muni_counts.values, text=muni_counts.values, textposition="auto")
        ])
        fig_bar_muni.update_layout(
            title="Top 15 municípios com mais lojas",
            xaxis_title="Município",
            yaxis_title="Número de lojas",
            height=400,
            showlegend=False,
            xaxis_tickangle=-45
        )

        # Gráfico de barras - Quantidade por distrito
        district_counts = df.groupby("distrito").size().sort_values(ascending=False).head(15)
        fig_bar_district = go.Figure([
            go.Bar(x=district_counts.index, y=district_counts.values, text=district_counts.values, textposition="auto")
        ])
        fig_bar_district.update_layout(
            title="Top 15 distritos com mais lojas",
            xaxis_title="Distrito",
            yaxis_title="Número de lojas",
            height=400,
            showlegend=False,
            xaxis_tickangle=-45
        )

        # Gráfico de pizza - Distribuição por cadeia (se filtro for 'Todas')
        if chain_filter == "Todas":
            chain_pie_counts = df.groupby("cadeia").size()
            fig_pie_chain = go.Figure([
                go.Pie(labels=chain_pie_counts.index, values=chain_pie_counts.values, hole=0.4)
            ])
            fig_pie_chain.update_layout(
                title="Distribuição de lojas por cadeia",
                height=400,
                showlegend=True
            )
        else:
            muni_values = df["municipio"].fillna("").astype(str).str.strip().replace("", "Município desconhecido")
            muni_pie = muni_values.value_counts()
            if len(muni_pie) > 10:
                muni_pie = pd.concat([muni_pie.head(10), pd.Series({"Outros": int(muni_pie.iloc[10:].sum())})])
            fig_pie_chain = go.Figure([go.Pie(labels=muni_pie.index, values=muni_pie.values, hole=0.4)])
            fig_pie_chain.update_layout(
                title=f"Distribuição territorial — {chain_filter}",
                height=400,
                showlegend=True,
            )

        # Tabela - Comparativo por cadeia (se filtro for 'Todas')
        if chain_filter == "Todas":
            chain_stats = df.groupby("cadeia").agg({
                "nome": "count",
                "municipio": lambda x: f"{x.nunique()} municípios",
                "distrito": lambda x: f"{x.nunique()} distritos"
            }).rename(columns={"nome": "Total de lojas", "municipio": "Municípios", "distrito": "Distritos"})
            chain_stats.index.name = "Cadeia"
            chain_stats.reset_index(inplace=True)

            table = html.Div([
                html.H5("Comparativo por cadeia:", className="mt-3 mb-2"),
                dash_table.DataTable(
                    data=chain_stats.to_dict('records'),
                    columns=[{"name": c, "id": c} for c in chain_stats.columns],
                    page_size=20,
                    style_table={"overflowX": "auto"},
                    style_header={
                        "backgroundColor": "rgb(230, 230, 230)",
                        "fontWeight": "bold"
                    },
                    style_cell={
                        "minWidth": "100px",
                        "width": "auto",
                        "textAlign": "left"
                    },
                    style_data_conditional=[
                        {
                            "if": {"row_index": "odd"},
                            "backgroundColor": "rgb(245, 245, 245)"
                        }
                    ]
                )
            ])
        else:
            table = html.Div([
                html.H5(f"Amostra de lojas — {chain_filter}", className="mb-2"),
                dash_table.DataTable(
                    data=df[["nome", "municipio", "distrito", "morada", "telefone"]].to_dict('records'),
                    columns=[
                        {"name": "Loja", "id": "nome"},
                        {"name": "Município", "id": "municipio"},
                        {"name": "Distrito", "id": "distrito"},
                        {"name": "Morada", "id": "morada"},
                        {"name": "Telefone", "id": "telefone"},
                    ],
                    page_size=12,
                    style_table={"overflowX": "auto"},
                    style_header={
                        "backgroundColor": "rgb(230, 230, 230)",
                        "fontWeight": "bold"
                    },
                    style_cell={
                        "minWidth": "100px",
                        "width": "auto",
                        "textAlign": "left"
                    },
                    style_data_conditional=[
                        {
                            "if": {"row_index": "odd"},
                            "backgroundColor": "rgb(245, 245, 245)"
                        }
                    ]
                )
            ])

        return kpis, fig_bar_chain, fig_bar_muni, fig_bar_district, fig_pie_chain, table

    except Exception as e:
        return dbc.Alert(f"Erro no cálculo de estatísticas: {e}", color="danger"), \
               empty_fig("Erro"), empty_fig("Erro"), empty_fig("Erro"), empty_fig("Erro"), \
               html.Div(str(e), className="small-note")



@app.callback(
    Output("download-intersections","data"),
    Input("download-intersections-btn","n_clicks"),
    State("inter-pair","value"),
    State("inter-radius","value"),
    prevent_initial_call=True,
)
def download_intersections(n_clicks, pair_key, radius):
    if n_clicks is None or n_clicks <= 0:
        return None
    try:
        pair_key = pair_key or "Todas"
        radius = int(radius or DEFAULT_RADIUS)
        df = all_intersections(radius, pair_key or "Todas")
        cols = ["cadeia_a", "loja_a", "morada_a", "municipio_a", "distrito_a", "lat_a", "lon_a",
                "cadeia_b", "loja_b", "morada_b", "municipio_b", "distrito_b", "lat_b", "lon_b", "dist_m"]
        df = df[cols]
        if df.empty:
            return None
        filename = f"intersecoes_{pair_key.replace(' x ', '_')}_{radius}m.csv"
        return dcc.send_data_frame(df.to_csv, filename, index=False, encoding="utf-8-sig")
    except Exception:
        return None


if __name__ == "__main__":
    app.run(
        debug=True,
        host="127.0.0.1",
        port=8055
    )
