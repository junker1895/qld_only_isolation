#!/usr/bin/env python3
"""Build a road-aware all-Queensland places.csv from official QLD locality polygons.

This improves on centroid-only locality points.

For each official QLD locality polygon:
  1. find road-graph nodes inside the locality polygon;
  2. prefer a node in the hub-connected road component if one exists;
  3. otherwise choose the closest available road node inside the polygon;
  4. if the locality has no road-graph node inside it, keep the official polygon
     representative point and mark it as QA in point_method.

Existing hub coordinates from the current places.csv are preserved. That keeps
your access anchors stable.

Expected output columns still include what qld_isolation_proper_v6.py needs:
  place_id,name,state,lga,lat,lon,is_hub

Extra columns are diagnostic/source metadata and are ignored safely by the
isolation script.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import numbers
import re
import sys
import time
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

import networkx as nx
import requests
from pyproj import Transformer
from shapely.geometry import Point, shape
from shapely.strtree import STRtree

LOCALITY_QUERY_URL = (
    "https://spatial-gis.information.qld.gov.au/arcgis/rest/services/"
    "Boundaries/AdminBoundariesFramework/FeatureServer/26/query"
)

OUT_FIELDS = "objectid,admintypename,adminareaname,loc_code,locality,lga,ca_area_sqkm"
YES_VALUES = {"1", "true", "t", "yes", "y"}

TO_M3857 = Transformer.from_crs("EPSG:4326", "EPSG:3857", always_xy=True)

OUTPUT_FIELDS = [
    "place_id",
    "name",
    "state",
    "lga",
    "lat",
    "lon",
    "is_hub",
    "place_type",
    "loc_code",
    "area_sqkm",
    "source",
    "source_objectid",
    "official_name_raw",
    "point_method",
    "graph_node",
    "official_centre_lat",
    "official_centre_lon",
    "roadpoint_offset_m",
    "graph_component_id",
    "hub_component_candidate_count",
    "all_component_candidate_count",
]


def clean(value: Any) -> str:
    if value is None:
        return ""
    return str(value).strip()


def normalise_name(value: Any) -> str:
    s = clean(value).lower()
    s = re.sub(r"[^a-z0-9]+", " ", s)
    return re.sub(r"\s+", " ", s).strip()


def display_name(value: Any) -> str:
    s = clean(value)
    if not s:
        return ""
    if s.upper() == s:
        s = s.title()
    replacements = {
        "Mcdowall": "McDowall",
        "Mckinlay": "McKinlay",
        "Mcdesme": "McDesme",
        "Mcilwraith": "McIlwraith",
        "D'Aguilar": "D'Aguilar",
        "K'Gari": "K'gari",
    }
    for old, new in replacements.items():
        s = s.replace(old, new)
    return s


def slug(value: str) -> str:
    s = normalise_name(value).replace(" ", "_")
    return s or "unknown"


def attr(attrs: Dict[str, Any], key: str) -> str:
    if key in attrs:
        return clean(attrs.get(key))
    lk = key.lower()
    for k, v in attrs.items():
        if str(k).lower() == lk:
            return clean(v)
    return ""


def is_hub_row(row: Dict[str, Any]) -> bool:
    return clean(row.get("is_hub")).lower() in YES_VALUES


def read_existing_hubs(path: Optional[Path]) -> List[Dict[str, Any]]:
    if not path or not path.exists():
        return []
    hubs: List[Dict[str, Any]] = []
    with path.open("r", encoding="utf-8-sig", newline="") as handle:
        for row in csv.DictReader(handle):
            if is_hub_row(row):
                hubs.append(dict(row))
    return hubs



def haversine_m(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    radius = 6_371_008.8
    p1 = math.radians(lat1)
    p2 = math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dlambda = math.radians(lon2 - lon1)
    a = math.sin(dphi / 2.0) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dlambda / 2.0) ** 2
    return 2.0 * radius * math.atan2(math.sqrt(a), math.sqrt(max(0.0, 1.0 - a)))


def nearest_graph_node_id(G: nx.Graph, lat: float, lon: float) -> Any:
    """Return the graph node nearest to a latitude/longitude coordinate."""
    best_node = None
    best_dist = float("inf")
    for node, data in G.nodes(data=True):
        try:
            node_lat = float(data.get("y"))
            node_lon = float(data.get("x"))
        except Exception:
            continue
        dist = haversine_m(lat, lon, node_lat, node_lon)
        if dist < best_dist:
            best_dist = dist
            best_node = node
    if best_node is None:
        raise ValueError("graph has no nodes with x/y coordinates")
    return best_node


def apply_manual_connectors_to_graph(G: nx.Graph, path: Optional[Path]) -> int:
    """Apply audited connector edges before component analysis.

    This should match the manual connectors used by qld_isolation_proper_v6.py,
    such as the Jardine River Ferry graph connector.
    """
    if not path:
        return 0
    if not path.exists():
        print(f"[MANUAL] connector file not found, skipping: {path}")
        return 0

    added = 0
    with path.open(encoding="utf-8-sig", newline="") as handle:
        reader = csv.DictReader(handle)
        for idx, row in enumerate(reader, start=1):
            u = clean(row.get("from_node") or row.get("u"))
            v = clean(row.get("to_node") or row.get("v"))

            from_lon = float(row.get("from_lon") or (G.nodes[u].get("x") if u in G else ""))
            from_lat = float(row.get("from_lat") or (G.nodes[u].get("y") if u in G else ""))
            to_lon = float(row.get("to_lon") or (G.nodes[v].get("x") if v in G else ""))
            to_lat = float(row.get("to_lat") or (G.nodes[v].get("y") if v in G else ""))

            if not u:
                u = nearest_graph_node_id(G, from_lat, from_lon)
                print(f"[MANUAL] row {idx}: snapped from coordinate to node {u}")
            if not v:
                v = nearest_graph_node_id(G, to_lat, to_lon)
                print(f"[MANUAL] row {idx}: snapped to coordinate to node {v}")
            if u not in G or v not in G:
                print(f"[MANUAL] row {idx}: bad node(s), skipped: {u}, {v}")
                continue
            length_m = float(row.get("length_m") or haversine_m(from_lat, from_lon, to_lat, to_lon))
            geometry_wkt = f"LINESTRING ({from_lon} {from_lat}, {to_lon} {to_lat})"

            attrs = {
                "geometry": geometry_wkt,
                "length": length_m,
                "name": clean(row.get("name")) or "manual_graph_connector",
                "highway": "manual_connector",
                "manual_connector": "true",
                "manual_reason": clean(row.get("reason")) or "manual graph topology repair",
                "manual_source": clean(row.get("source")) or str(path),
            }

            if G.is_multigraph():
                G.add_edge(u, v, key=f"manual_connector_{idx}_fwd", **attrs)
                added += 1
                if G.is_directed():
                    G.add_edge(v, u, key=f"manual_connector_{idx}_rev", **attrs)
                    added += 1
            else:
                G.add_edge(u, v, **attrs)
                added += 1
                if G.is_directed():
                    G.add_edge(v, u, **attrs)
                    added += 1

            print(f"[MANUAL] applied connector {u} <-> {v} length={length_m:.1f}m")

    print(f"[MANUAL] connector edges applied before component analysis: {added}")
    return added


def existing_hub_to_output_row(row: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    name = clean(row.get("name") or row.get("place_name"))
    lat = clean(row.get("lat") or row.get("latitude"))
    lon = clean(row.get("lon") or row.get("lng") or row.get("longitude"))
    if not name or not lat or not lon:
        return None

    return {
        "place_id": clean(row.get("place_id") or row.get("id")) or f"existing_hub_{slug(name)}",
        "name": name,
        "state": clean(row.get("state")) or "QLD",
        "lga": clean(row.get("lga")),
        "lat": lat,
        "lon": lon,
        "is_hub": "1",
        "place_type": clean(row.get("place_type")) or "hub_anchor_existing",
        "loc_code": clean(row.get("loc_code")),
        "area_sqkm": clean(row.get("area_sqkm")),
        "source": "existing_places_csv_unmatched_hub",
        "source_objectid": clean(row.get("source_objectid")),
        "official_name_raw": clean(row.get("official_name_raw") or name),
        "point_method": "existing_hub_coordinate_preserved",
        "graph_node": clean(row.get("nearest_node") or row.get("graph_node")),
        "official_centre_lat": "",
        "official_centre_lon": "",
        "roadpoint_offset_m": "",
        "graph_component_id": "",
        "hub_component_candidate_count": "",
        "all_component_candidate_count": "",
    }


def request_json(params: Dict[str, Any], *, retries: int = 4, timeout_s: float = 90.0) -> Dict[str, Any]:
    last_exc: Optional[BaseException] = None
    for attempt in range(1, retries + 1):
        try:
            response = requests.get(
                LOCALITY_QUERY_URL,
                params=params,
                timeout=timeout_s,
                headers={"User-Agent": "qld-locality-roadpoint-builder/1.0"},
            )
            response.raise_for_status()
            payload = response.json()
            if "error" in payload:
                raise RuntimeError(json.dumps(payload["error"], ensure_ascii=False))
            return payload
        except Exception as exc:
            last_exc = exc
            if attempt >= retries:
                break
            sleep_s = min(20, 2 ** attempt)
            print(f"[WARN] request failed attempt {attempt}/{retries}: {exc}; retrying in {sleep_s}s", file=sys.stderr)
            time.sleep(sleep_s)
    raise RuntimeError(f"ArcGIS request failed: {last_exc}")


def get_feature_count() -> int:
    payload = request_json({"f": "json", "where": "1=1", "returnCountOnly": "true"})
    return int(payload.get("count") or 0)


def fetch_geojson_page(offset: int, page_size: int) -> List[Dict[str, Any]]:
    params = {
        "f": "geojson",
        "where": "1=1",
        "outFields": OUT_FIELDS,
        "returnGeometry": "true",
        "outSR": "4326",
        "resultOffset": offset,
        "resultRecordCount": page_size,
        "orderByFields": "objectid",
        "geometryPrecision": 7,
    }
    payload = request_json(params)
    return list(payload.get("features") or [])


def fetch_all_locality_polygons(page_size: int) -> List[Dict[str, Any]]:
    count = get_feature_count()
    print(f"[SOURCE] official locality count reported by service: {count:,}")

    features: List[Dict[str, Any]] = []
    offset = 0
    while True:
        page = fetch_geojson_page(offset, page_size)
        if not page:
            break
        features.extend(page)
        print(f"[FETCH] {len(features):,}/{count:,} polygon features")
        offset += len(page)
        if len(page) < page_size:
            break
        if count and len(features) >= count:
            break
    return features


def load_graph_nodes(graph_path: Path, manual_connectors_path: Optional[Path]) -> Tuple[nx.Graph, List[Any], List[Point], List[Tuple[float, float]], STRtree]:
    print(f"[LOAD] graph: {graph_path}")
    G = nx.read_graphml(graph_path)
    print(f"[GRAPH] nodes={G.number_of_nodes():,} edges={G.number_of_edges():,}")
    apply_manual_connectors_to_graph(G, manual_connectors_path)

    node_ids: List[Any] = []
    points: List[Point] = []
    xy_m: List[Tuple[float, float]] = []

    for n, data in G.nodes(data=True):
        try:
            lon = float(data["x"])
            lat = float(data["y"])
        except Exception:
            continue
        node_ids.append(n)
        points.append(Point(lon, lat))
        xy_m.append(TO_M3857.transform(lon, lat))

    print(f"[INDEX] building graph-node spatial index from {len(points):,} nodes")
    tree = STRtree(points)
    return G, node_ids, points, xy_m, tree



def build_component_lookup(G: nx.Graph) -> Tuple[Dict[Any, int], List[int]]:
    print("[COMPONENTS] building undirected graph components")
    UG = G.to_undirected()
    comps = list(nx.connected_components(UG))
    comps.sort(key=len, reverse=True)

    node_to_comp: Dict[Any, int] = {}
    sizes: List[int] = []
    for comp_id, comp in enumerate(comps):
        sizes.append(len(comp))
        for n in comp:
            node_to_comp[n] = comp_id

    print("[COMPONENTS] largest components:", ", ".join(f"{i}:{s:,}" for i, s in enumerate(sizes[:10])))
    return node_to_comp, sizes


def nearest_graph_node_for_latlon(node_ids: List[Any], xy_m: List[Tuple[float, float]], lat: float, lon: float) -> Optional[Any]:
    qx, qy = TO_M3857.transform(lon, lat)
    best_idx: Optional[int] = None
    best_d2 = float("inf")
    for i, (x, y) in enumerate(xy_m):
        d2 = (x - qx) ** 2 + (y - qy) ** 2
        if d2 < best_d2:
            best_d2 = d2
            best_idx = i
    return node_ids[best_idx] if best_idx is not None else None


def hub_component_ids_from_existing_hubs(
    hubs: List[Dict[str, Any]],
    node_ids: List[Any],
    xy_m: List[Tuple[float, float]],
    node_to_comp: Dict[Any, int],
) -> set[int]:
    out: set[int] = set()
    for hub in hubs:
        try:
            lat = float(clean(hub.get("lat") or hub.get("latitude")))
            lon = float(clean(hub.get("lon") or hub.get("lng") or hub.get("longitude")))
        except Exception:
            continue
        n = nearest_graph_node_for_latlon(node_ids, xy_m, lat, lon)
        if n is not None and n in node_to_comp:
            out.add(node_to_comp[n])
    print(f"[COMPONENTS] hub-connected component ids: {sorted(out)}")
    return out


def iter_tree_indices(tree: STRtree, points: List[Point], query_geom: Any) -> Iterable[int]:
    hits = tree.query(query_geom)
    # Shapely 2 returns integer indices, often as numpy.int64 rather than plain int.
    # Shapely 1 returns geometry objects.
    for hit in hits:
        if isinstance(hit, numbers.Integral):
            idx = int(hit)
            if 0 <= idx < len(points):
                yield idx
        else:
            # Shapely 1 fallback. This is slower only for the returned envelope candidates.
            wkb = hit.wkb
            for i, p in enumerate(points):
                if p.wkb == wkb:
                    yield i
                    break


def choose_road_node_inside_polygon(
    geom: Any,
    centre_lon: float,
    centre_lat: float,
    node_ids: List[Any],
    points: List[Point],
    xy_m: List[Tuple[float, float]],
    tree: STRtree,
    node_to_comp: Dict[Any, int],
    hub_component_ids: set[int],
) -> Tuple[Optional[Any], Optional[float], Optional[float], Optional[float], Optional[int], int, int]:
    """Choose a representative road node inside a locality polygon.

    Preference order:
      1. node in a hub-connected component;
      2. otherwise any road node inside the locality;
      3. within each class, closest to the locality representative centre.
    """
    cx, cy = TO_M3857.transform(centre_lon, centre_lat)

    best_idx: Optional[int] = None
    best_score = (9, float("inf"))
    all_candidates = 0
    hub_candidates = 0

    for idx in iter_tree_indices(tree, points, geom):
        p = points[idx]
        try:
            inside = geom.covers(p)
        except Exception:
            inside = geom.contains(p)
        if not inside:
            continue

        all_candidates += 1
        node = node_ids[idx]
        comp_id = node_to_comp.get(node)
        is_hub_component = comp_id in hub_component_ids
        if is_hub_component:
            hub_candidates += 1

        x, y = xy_m[idx]
        d2 = (x - cx) ** 2 + (y - cy) ** 2
        score = (0 if is_hub_component else 1, d2)

        if score < best_score:
            best_score = score
            best_idx = idx

    if best_idx is None:
        return None, None, None, None, None, hub_candidates, all_candidates

    p = points[best_idx]
    node = node_ids[best_idx]
    comp_id = node_to_comp.get(node)
    return node, float(p.y), float(p.x), math.sqrt(best_score[1]), comp_id, hub_candidates, all_candidates


def feature_to_place(
    feature: Dict[str, Any],
    node_ids: List[Any],
    points: List[Point],
    xy_m: List[Tuple[float, float]],
    tree: STRtree,
    hub_by_name: Dict[str, Dict[str, Any]],
    node_to_comp: Dict[Any, int],
    hub_component_ids: set[int],
) -> Optional[Dict[str, Any]]:
    props = feature.get("properties") or {}
    geom_json = feature.get("geometry")
    if not geom_json:
        return None

    locality_raw = attr(props, "locality") or attr(props, "adminareaname")
    if not locality_raw:
        return None

    try:
        geom = shape(geom_json)
        if geom.is_empty:
            return None
        if not geom.is_valid:
            geom = geom.buffer(0)
    except Exception:
        return None

    centre = geom.representative_point()
    centre_lon = float(centre.x)
    centre_lat = float(centre.y)

    loc_code = attr(props, "loc_code")
    objectid = attr(props, "objectid")
    name = display_name(locality_raw)
    lga = display_name(attr(props, "lga"))
    place_id = f"qld_locality_{loc_code}" if loc_code else f"qld_locality_{slug(name)}_{objectid}"

    hub = hub_by_name.get(normalise_name(name)) or hub_by_name.get(normalise_name(locality_raw))

    if hub:
        # Hubs are access anchors. Preserve the curated hub coordinate rather than
        # moving the anchor to a locality roadpoint.
        lat = clean(hub.get("lat") or hub.get("latitude"))
        lon = clean(hub.get("lon") or hub.get("lng") or hub.get("longitude"))
        return {
            "place_id": place_id,
            "name": name,
            "state": "QLD",
            "lga": lga,
            "lat": lat,
            "lon": lon,
            "is_hub": "1",
            "place_type": "hub_anchor_official_locality",
            "loc_code": loc_code,
            "area_sqkm": attr(props, "ca_area_sqkm"),
            "source": "qld_admin_boundaries_locality_boundary_plus_existing_hub_coordinate",
            "source_objectid": objectid,
            "official_name_raw": locality_raw,
            "point_method": "existing_hub_coordinate_preserved",
            "graph_node": "",
            "official_centre_lat": f"{centre_lat:.7f}",
            "official_centre_lon": f"{centre_lon:.7f}",
            "roadpoint_offset_m": "",
            "graph_component_id": "",
            "hub_component_candidate_count": "",
            "all_component_candidate_count": "",
        }

    node, road_lat, road_lon, offset_m, comp_id, hub_candidate_count, all_candidate_count = choose_road_node_inside_polygon(
        geom,
        centre_lon,
        centre_lat,
        node_ids,
        points,
        xy_m,
        tree,
        node_to_comp,
        hub_component_ids,
    )

    if node is not None:
        lat = road_lat
        lon = road_lon
        if comp_id in hub_component_ids:
            point_method = "road_node_inside_locality_hub_component"
        else:
            point_method = "road_node_inside_locality_nonhub_component"
        graph_node = str(node)
        roadpoint_offset_m = f"{float(offset_m):.1f}" if offset_m is not None else ""
    else:
        lat = centre_lat
        lon = centre_lon
        point_method = "official_representative_point_no_graph_node_inside_locality"
        graph_node = ""
        roadpoint_offset_m = ""
        comp_id = None
        hub_candidate_count = 0
        all_candidate_count = 0

    return {
        "place_id": place_id,
        "name": name,
        "state": "QLD",
        "lga": lga,
        "lat": f"{float(lat):.7f}",
        "lon": f"{float(lon):.7f}",
        "is_hub": "0",
        "place_type": "locality_road_representative_point" if node is not None else "locality_representative_point",
        "loc_code": loc_code,
        "area_sqkm": attr(props, "ca_area_sqkm"),
        "source": "qld_admin_boundaries_locality_boundary",
        "source_objectid": objectid,
        "official_name_raw": locality_raw,
        "point_method": point_method,
        "graph_node": graph_node,
        "official_centre_lat": f"{centre_lat:.7f}",
        "official_centre_lon": f"{centre_lon:.7f}",
        "roadpoint_offset_m": roadpoint_offset_m,
        "graph_component_id": "" if comp_id is None else str(comp_id),
        "hub_component_candidate_count": str(hub_candidate_count),
        "all_component_candidate_count": str(all_candidate_count),
    }


def write_csv(path: Path, rows: Iterable[Dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=OUTPUT_FIELDS, extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def build_places(graph_path: Path, existing_path: Optional[Path], output_path: Path, page_size: int, manual_connectors_path: Optional[Path]) -> None:
    existing_hubs = read_existing_hubs(existing_path)
    hub_by_name = {normalise_name(r.get("name")): r for r in existing_hubs if clean(r.get("name"))}

    G, node_ids, points, xy_m, tree = load_graph_nodes(graph_path, manual_connectors_path)
    node_to_comp, comp_sizes = build_component_lookup(G)
    hub_component_ids = hub_component_ids_from_existing_hubs(existing_hubs, node_ids, xy_m, node_to_comp)
    if not hub_component_ids:
        print("[WARN] no hub-connected component ids found; falling back to largest graph component 0")
        hub_component_ids = {0}
    features = fetch_all_locality_polygons(page_size)

    rows: List[Dict[str, Any]] = []
    skipped = 0

    for i, f in enumerate(features, start=1):
        row = feature_to_place(f, node_ids, points, xy_m, tree, hub_by_name, node_to_comp, hub_component_ids)
        if row is None:
            skipped += 1
            continue
        rows.append(row)
        if i % 250 == 0:
            print(f"[PLACE] processed {i:,}/{len(features):,}")

    locality_names = {normalise_name(r["name"]) for r in rows}
    locality_raw_names = {normalise_name(r["official_name_raw"]) for r in rows}

    appended_hubs: List[Dict[str, Any]] = []
    for hub in existing_hubs:
        hn = normalise_name(hub.get("name"))
        if hn not in locality_names and hn not in locality_raw_names:
            out = existing_hub_to_output_row(hub)
            if out:
                appended_hubs.append(out)

    by_id: Dict[str, Dict[str, Any]] = {}
    for row in rows + appended_hubs:
        pid = row["place_id"]
        if pid in by_id:
            by_id[pid]["is_hub"] = "1" if row.get("is_hub") == "1" or by_id[pid].get("is_hub") == "1" else "0"
        else:
            by_id[pid] = row

    final_rows = list(by_id.values())
    final_rows.sort(key=lambda r: (0 if clean(r.get("is_hub")) == "1" else 1, normalise_name(r.get("name")), normalise_name(r.get("lga"))))

    write_csv(output_path, final_rows)

    method_counts: Dict[str, int] = {}
    for row in final_rows:
        method_counts[row["point_method"]] = method_counts.get(row["point_method"], 0) + 1

    print()
    print(f"[OUT] wrote: {output_path}")
    print(f"[OUT] rows: {len(final_rows):,}")
    print(f"[OUT] existing hubs read: {len(existing_hubs):,}")
    print(f"[OUT] unmatched existing hubs appended: {len(appended_hubs):,}")
    print(f"[OUT] skipped locality features: {skipped:,}")
    print("[OUT] point methods:")
    for k, v in sorted(method_counts.items()):
        print(f"  - {k}: {v:,}")
    if appended_hubs:
        print("[OUT] appended hubs:")
        for row in appended_hubs:
            print(f"  - {row['name']} ({row['lat']}, {row['lon']})")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Build connected-component-aware roadpoint places.csv from official Queensland locality polygons.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--graph", default="qld_drive.graphml", help="Queensland road graph GraphML path.")
    parser.add_argument("--existing", default="places.csv", help="Existing places.csv to preserve hub rows from.")
    parser.add_argument("--manual-connectors", default="manual_graph_connectors.csv", help="Optional manual connector CSV to apply before graph component analysis.")
    parser.add_argument("--output", default="places_all_qld_localities_connected_roadpoints.csv", help="Output CSV path.")
    parser.add_argument("--page-size", type=int, default=1000, help="ArcGIS query page size. Max service record count is 2000.")
    args = parser.parse_args()

    if args.page_size < 1 or args.page_size > 2000:
        raise SystemExit("--page-size must be between 1 and 2000")

    build_places(
        graph_path=Path(args.graph),
        existing_path=Path(args.existing) if args.existing else None,
        output_path=Path(args.output),
        page_size=args.page_size,
        manual_connectors_path=Path(args.manual_connectors) if args.manual_connectors else None,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
