#!/usr/bin/env python3
"""Queensland road-closure isolation analyser (v7 manual graph connectors).

Purpose
-------
Fetches current QLD Traffic road-closure events, matches blocking closures to a
Queensland road graph, and tests whether a list of Queensland places can still
reach one or more nominated hub places.

This script is designed to be safer than a simple "nearest node is blocked"
approach. It:
  * classifies QLD Traffic events into impassable / conditional / unknown;
  * treats QLD Traffic "All lanes affected" as conditional unless the payload explicitly says closed/not passable;
  * treats "4WD only" / "restricted to four wheel drive vehicles only" as conditional/restricted access, not a full closure;
  * treats generic flood safety advice such as "Do not drive in flood waters" as conditional unless the payload also says the road is closed/not passable;
  * matches closure geometries to road EDGES, not just nodes;
  * runs two scenarios:
        1. impassable/full closures only;
        2. impassable + restricted/conditional closures;
  * compares before-closure and after-closure hub reachability;
  * avoids labelling places as isolated if they were already disconnected before
    current closures were applied;
  * writes a full place table, isolated-only table, GeoJSON outputs, closure
    match diagnostics, unmatched closures, and a summary JSON.

Expected inputs
---------------
1. A Queensland road graph GraphML, usually from your existing build script:
       network_cache/qld_drive.graphml

2. A places CSV with at least name, lat, lon. Hubs are rows with is_hub=1.
   Useful optional fields: place_id, state, lga, type/place_type.

   Example:
       place_id,name,state,lga,lat,lon,is_hub
       qld_brisbane,Brisbane,qld,Brisbane,-27.4705,153.0260,1
       qld_cairns,Cairns,qld,Cairns,-16.9203,145.7710,1
       qld_alpha,Alpha,qld,Barcaldine,-23.6485,146.6409,0

Typical run
-----------
    python qld_isolation_proper_v7.py \
      --graph network_cache/qld_drive.graphml \
      --places places.csv \
      --out-dir out_isolation

Use existing closure file instead of fetching live:
    python qld_isolation_proper_v7.py \
      --graph network_cache/qld_drive.graphml \
      --places places.csv \
      --closures-geojson out/closures_qld_current.geojson \
      --out-dir out_isolation

Main outputs
------------
    out_isolation/closures_qld_current.geojson
    out_isolation/closures_qld_current.csv
    out_isolation/qld_place_isolation_current.csv
    out_isolation/isolated_places_qld.csv
    out_isolation/qld_place_isolation_current.geojson
    out_isolation/isolated_places_qld.geojson
    out_isolation/closure_match_report_qld.csv
    out_isolation/unmatched_closures_qld.csv
    out_isolation/qld_isolation_summary.json

Dependencies
------------
Required: requests, networkx, shapely, pyproj
Optional but strongly recommended for speed: scipy
"""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import hashlib
import heapq
import json
import math
import numbers
import re
import sys
import time
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Tuple

import networkx as nx
import requests
from pyproj import Transformer
from shapely import wkt
from shapely.geometry import (
    GeometryCollection,
    LineString,
    MultiLineString,
    MultiPoint,
    MultiPolygon,
    Point,
    Polygon,
    mapping,
    shape,
)
from shapely.ops import transform
from shapely.strtree import STRtree

# ---------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------

QLD_TRAFFIC_URL = "https://data.qldtraffic.qld.gov.au/events_v2.geojson"
QLD_BBOX = (-29.5, 137.5, -9.0, 154.0)  # south, west, north, east

TO_M3857 = Transformer.from_crs("EPSG:4326", "EPSG:3857", always_xy=True)
TO_WGS84 = Transformer.from_crs("EPSG:3857", "EPSG:4326", always_xy=True)

HARD_CLOSED_PATTERNS = [
    r"\broad\s+closed\b",
    r"\ball\s+lanes?\s+closed\b",
    r"\b(lanes?|road)\s+closed\b",
    r"\bclosed\b",
    r"\bno\s+access\b",
    r"\bnot\s+passable\b",
    r"\bimpassable\b",
    # Generic "do not drive in flood waters" advice is common on QLD Traffic and
    # does not, by itself, mean the road is formally closed. Keep travel/proceed
    # as hard closures, but classify do-not-drive flood advice later using
    # impact_type / impact_subtype.
    r"\bdo\s+not\s+(travel|proceed)\b",
    r"\bemergency\s+services\s+only\b",
]

# Important: lane closed is not a full road closure.
SOFT_RESTRICT_PATTERNS = [
    r"\bproceed\s+with\s+caution\b",
    r"\bcaution\b",
    r"\bexpect\s+delays\b",
    r"\btraffic\s+control\b",
    r"\bsingle\s+lane\b",
    r"\bone\s+lane\b",
    r"\blane\s+closed\b",
    r"\blanes?\s+affected\b",
    r"\b4wd\b",
    r"\b4\s*wd\b",
    r"\b4\s*wheel\s*drive\b",
    r"\bfour\s+wheel\s+drive\b",
    r"\b4x4\b",
    r"\bh(igh)?\s*clearance\b",
    r"\blocal\s+traffic\s+only\b",
    r"\brestricted\s+access\b",
    r"\bdetour\b",
    r"\breduced\s+speed\b",
    r"\bslow\b",
]

FLOOD_PATTERNS = [
    r"\bflood\b",
    r"\bflooding\b",
    r"\bwater\s+over\s+road\b",
    r"\binundat(ed|ion)\b",
    r"\bsubmerged\b",
]

FLOOD_SOFTENERS = [
    r"\bminor\b",
    r"\bshallow\b",
    r"\btrafficable\b",
    r"\bpassable\b",
    r"\bopen\b",
    r"\bproceed\s+with\s+caution\b",
]

YES_VALUES = {"1", "true", "t", "yes", "y"}

CLOSURE_CSV_FIELDS = [
    "event_id",
    "source",
    "jurisdiction",
    "category_raw",
    "category_norm",
    "passability_norm",
    "status_norm",
    "reason_norm",
    "start_time",
    "end_time",
    "last_updated",
    "fetched_at",
    "title",
    "description",
    "road_name",
    "locality",
    "direction",
    "lanes_affected",
    "restrictions_text",
    "url",
    "source_event_id",
    "raw_title",
    "raw_description",
    "raw_advice",
    "raw_event_type",
    "raw_event_subtype",
    "raw_impact_type",
    "raw_impact_subtype",
    "raw_road",
    "raw_locality",
    "raw_status",
    "raw_properties_json",
    "geometry_json",
]

PLACE_CSV_FIELDS = [
    "place_id",
    "name",
    "place_type",
    "state",
    "lga",
    "lat",
    "lon",
    "is_hub",
    "nearest_node",
    "snap_distance_m",
    "snap_strategy",
    "snap_note",
    "hub_access_before",
    "hub_access_impassable_only",
    "hub_access_all_blocking",
    "reachable_hubs_before",
    "reachable_hubs_impassable_only",
    "reachable_hubs_all_blocking",
    "state_border_access_before",
    "reachable_state_borders_before",
    "hub_network_warning",
    "isolation_category",
    "isolation_confidence",
    "isolation_reason",
    "nearby_blocking_closures_json",
    "hub_route_name",
    "hub_route_distance_m",
    "hub_route_geojson",
]

MATCH_CSV_FIELDS = [
    "scenario",
    "closure_id",
    "source",
    "category_norm",
    "passability_norm",
    "status_norm",
    "reason_norm",
    "title",
    "road_name",
    "locality",
    "description",
    "restrictions_text",
    "source_event_id",
    "raw_advice",
    "raw_event_type",
    "raw_event_subtype",
    "raw_impact_type",
    "raw_impact_subtype",
    "raw_properties_json",
    "geometry_type",
    "matched_edges",
    "nearest_edge_m",
    "confidence",
    "match_status",
    "notes",
    "url",
]

UNMATCHED_CSV_FIELDS = [
    "scenario",
    "closure_id",
    "category_norm",
    "passability_norm",
    "status_norm",
    "title",
    "road_name",
    "locality",
    "description",
    "restrictions_text",
    "source_event_id",
    "raw_advice",
    "raw_event_type",
    "raw_event_subtype",
    "raw_impact_type",
    "raw_impact_subtype",
    "raw_properties_json",
    "geometry_type",
    "nearest_edge_m",
    "reason",
    "url",
]


# ---------------------------------------------------------------------
# Data models
# ---------------------------------------------------------------------

@dataclass
class Closure:
    event_id: str
    source: str
    jurisdiction: str
    category_raw: str
    category_norm: str
    passability_norm: str
    status_norm: str
    reason_norm: str
    start_time: str = ""
    end_time: str = ""
    last_updated: str = ""
    fetched_at: str = ""
    title: str = ""
    description: str = ""
    road_name: str = ""
    locality: str = ""
    direction: str = ""
    lanes_affected: str = ""
    restrictions_text: str = ""
    url: str = ""
    source_event_id: str = ""
    raw_title: str = ""
    raw_description: str = ""
    raw_advice: str = ""
    raw_event_type: str = ""
    raw_event_subtype: str = ""
    raw_impact_type: str = ""
    raw_impact_subtype: str = ""
    raw_road: str = ""
    raw_locality: str = ""
    raw_status: str = ""
    geometry: Any = None  # shapely geometry in EPSG:4326
    raw_properties: Dict[str, Any] = field(default_factory=dict)

    @property
    def geometry_type(self) -> str:
        return getattr(self.geometry, "geom_type", "") if self.geometry is not None else ""

    def to_feature(self) -> Dict[str, Any]:
        props = self.to_csv_row()
        props.pop("geometry_json", None)
        return {
            "type": "Feature",
            "geometry": mapping(self.geometry) if self.geometry is not None else None,
            "properties": props,
        }

    def to_csv_row(self) -> Dict[str, Any]:
        return {
            "event_id": self.event_id,
            "source": self.source,
            "jurisdiction": self.jurisdiction,
            "category_raw": self.category_raw,
            "category_norm": self.category_norm,
            "passability_norm": self.passability_norm,
            "status_norm": self.status_norm,
            "reason_norm": self.reason_norm,
            "start_time": self.start_time,
            "end_time": self.end_time,
            "last_updated": self.last_updated,
            "fetched_at": self.fetched_at,
            "title": self.title,
            "description": self.description,
            "road_name": self.road_name,
            "locality": self.locality,
            "direction": self.direction,
            "lanes_affected": self.lanes_affected,
            "restrictions_text": self.restrictions_text,
            "url": self.url,
            "source_event_id": self.source_event_id,
            "raw_title": self.raw_title,
            "raw_description": self.raw_description,
            "raw_advice": self.raw_advice,
            "raw_event_type": self.raw_event_type,
            "raw_event_subtype": self.raw_event_subtype,
            "raw_impact_type": self.raw_impact_type,
            "raw_impact_subtype": self.raw_impact_subtype,
            "raw_road": self.raw_road,
            "raw_locality": self.raw_locality,
            "raw_status": self.raw_status,
            "raw_properties_json": json.dumps(self.raw_properties or {}, ensure_ascii=False, default=str),
            "geometry_json": json.dumps(mapping(self.geometry), ensure_ascii=False) if self.geometry is not None else "",
        }


@dataclass
class Place:
    place_id: str
    name: str
    lat: float
    lon: float
    is_hub: bool = False
    state: str = "qld"
    lga: str = ""
    place_type: str = ""
    raw: Dict[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class EdgeRef:
    u: Any
    v: Any
    k: Any

    def as_tuple(self) -> Tuple[Any, Any, Any]:
        return (self.u, self.v, self.k)


@dataclass
class EdgeIndex:
    edge_refs: List[EdgeRef]
    edge_geoms_m: List[Any]
    edge_names: List[str]
    tree: STRtree
    wkb_to_indices: Dict[bytes, List[int]]


@dataclass
class NodeIndex:
    node_ids: List[Any]
    xy_m: List[Tuple[float, float]]
    tree: Any = None


@dataclass
class ScenarioResult:
    name: str
    blocked_edges: set[Tuple[Any, Any, Any]]
    reachable_nodes: set[Any]
    match_rows: List[Dict[str, Any]]
    unmatched_rows: List[Dict[str, Any]]
    matched_closures: List[Closure]


# ---------------------------------------------------------------------
# Utility functions
# ---------------------------------------------------------------------

def utc_now_iso() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def stable_id(source_id: str) -> str:
    digest = hashlib.sha1(f"qld:qldtraffic:{source_id}".encode("utf-8")).hexdigest()[:20]
    return f"qld.qldtraffic.{digest}"


def clean_str(value: Any) -> str:
    if value is None:
        return ""
    return str(value).strip()


def _flatten_prop_values(obj: Any, prefix: str = "") -> Dict[str, Any]:
    """Flatten raw JSON properties for robust field discovery/debugging."""
    out: Dict[str, Any] = {}
    if isinstance(obj, dict):
        for k, v in obj.items():
            key = f"{prefix}.{k}" if prefix else str(k)
            if isinstance(v, (dict, list)):
                out.update(_flatten_prop_values(v, key))
            else:
                out[key] = v
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            key = f"{prefix}.{i}" if prefix else str(i)
            if isinstance(v, (dict, list)):
                out.update(_flatten_prop_values(v, key))
            else:
                out[key] = v
    return out


def find_prop(props: Dict[str, Any], candidate_keys: Sequence[str]) -> str:
    """Return first non-empty raw property value by exact or case-insensitive key, including nested keys."""
    flat = _flatten_prop_values(props)
    lower_map = {k.lower(): v for k, v in flat.items()}

    # Exact top-level first.
    for key in candidate_keys:
        if key in props and props.get(key) not in (None, ""):
            return clean_str(props.get(key))

    # Exact flattened path, then case-insensitive path/suffix.
    for key in candidate_keys:
        if key in flat and flat.get(key) not in (None, ""):
            return clean_str(flat.get(key))
    for key in candidate_keys:
        lk = key.lower()
        if lk in lower_map and lower_map.get(lk) not in (None, ""):
            return clean_str(lower_map.get(lk))
    for key in candidate_keys:
        lk = key.lower()
        for flat_key, val in flat.items():
            fkl = flat_key.lower()
            if (fkl.endswith("." + lk) or fkl == lk) and val not in (None, ""):
                return clean_str(val)
    return ""


def extract_raw_qld_fields(props: Dict[str, Any]) -> Dict[str, str]:
    impact = props.get("impact") if isinstance(props.get("impact"), dict) else {}
    combined = dict(props)
    if impact:
        for k, v in impact.items():
            combined.setdefault(f"impact_{k}", v)

    return {
        "source_event_id": find_prop(combined, ["id", "event_id", "eventId", "guid", "reference", "impactId", "source_id"]),
        "raw_title": find_prop(combined, ["headline", "title", "displayName", "display_name", "name", "shortTitle", "event_title", "eventName"]),
        "raw_description": find_prop(combined, ["description", "details", "message", "content", "summary", "event_description"]),
        "raw_advice": find_prop(combined, ["advice", "restriction", "restrictions", "travelAdvice", "travel_advice"]),
        "raw_event_type": find_prop(combined, ["event_type", "eventType", "type", "category", "impact_type", "impact.impact_type"]),
        "raw_event_subtype": find_prop(combined, ["event_subtype", "eventSubtype", "subtype", "sub_type", "impact_subtype", "impact.impact_subtype"]),
        "raw_impact_type": find_prop(combined, ["impact_type", "impact.impact_type"]),
        "raw_impact_subtype": find_prop(combined, ["impact_subtype", "impact.impact_subtype"]),
        "raw_road": find_prop(combined, ["road", "road_name", "roadName", "roadDisplayName", "road_display_name", "street", "route", "route_name"]),
        "raw_locality": find_prop(combined, ["locality", "suburb", "town", "location", "locationName", "location_name", "area"]),
        "raw_status": find_prop(combined, ["status", "state", "eventStatus", "event_status"]),
    }


def best_nonempty(*values: Any) -> str:
    for value in values:
        s = clean_str(value)
        if s:
            return s
    return ""


def match_any(patterns: Sequence[str], text: str) -> bool:
    return any(re.search(pattern, text) for pattern in patterns)


def haversine_m(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    radius = 6_371_008.8
    p1 = math.radians(lat1)
    p2 = math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dlambda = math.radians(lon2 - lon1)
    a = math.sin(dphi / 2.0) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dlambda / 2.0) ** 2
    return 2.0 * radius * math.atan2(math.sqrt(a), math.sqrt(max(0.0, 1.0 - a)))


def in_qld_bbox(lat: float, lon: float) -> bool:
    south, west, north, east = QLD_BBOX
    return south <= lat <= north and west <= lon <= east


def geom_to_m(geom: Any) -> Any:
    return transform(TO_M3857.transform, geom)


def point_wgs_to_m(lon: float, lat: float) -> Tuple[float, float]:
    x, y = TO_M3857.transform(float(lon), float(lat))
    return float(x), float(y)


def geometry_from_jsonish(value: Any) -> Any:
    if value is None or value == "":
        return None
    if isinstance(value, dict):
        return shape(value)
    if isinstance(value, str):
        s = value.strip()
        if not s:
            return None
        try:
            return shape(json.loads(s))
        except Exception:
            try:
                return wkt.loads(s)
            except Exception:
                return None
    return None


def iter_geometries(geom: Any) -> Iterable[Any]:
    if geom is None:
        return
    if isinstance(geom, GeometryCollection):
        for g in geom.geoms:
            yield from iter_geometries(g)
    elif isinstance(geom, (MultiLineString, MultiPoint, MultiPolygon)):
        for g in geom.geoms:
            yield g
    else:
        yield geom


def geom_representative_latlon(geom: Any) -> Optional[Tuple[float, float]]:
    if geom is None or geom.is_empty:
        return None
    try:
        p = geom.representative_point()
        return float(p.y), float(p.x)
    except Exception:
        try:
            p = geom.centroid
            return float(p.y), float(p.x)
        except Exception:
            return None


# ---------------------------------------------------------------------
# QLD Traffic fetch and normalisation
# ---------------------------------------------------------------------

def classify_qld_event(props: Dict[str, Any]) -> Tuple[str, str, str]:
    """Return (passability_norm, category_norm, category_raw)."""
    title = clean_str(props.get("headline") or props.get("title"))
    advice = clean_str(props.get("advice"))
    category_raw = clean_str(props.get("event_type") or props.get("type") or props.get("category"))
    event_type = clean_str(props.get("event_type"))
    event_subtype = clean_str(props.get("event_subtype"))
    impact = props.get("impact") if isinstance(props.get("impact"), dict) else {}
    impact_type = clean_str(impact.get("impact_type"))
    impact_subtype = clean_str(impact.get("impact_subtype"))
    restrictions_text = clean_str(props.get("restrictions") or props.get("advice"))

    desc = clean_str(props.get("description"))
    if not desc and isinstance(props.get("impact"), str):
        desc = clean_str(props.get("impact"))
    if not desc:
        desc = advice

    text = " ".join(
        [
            title,
            desc,
            category_raw,
            advice,
            impact_type,
            impact_subtype,
            event_type,
            event_subtype,
            restrictions_text,
        ]
    ).lower().strip()

    advice_l = advice.lower()
    if advice_l:
        if advice_l in {"road closed", "closed", "no access", "not passable", "impassable", "do not proceed"}:
            return "impassable", "road_closed", category_raw
        if advice_l in {"proceed with caution", "use caution", "drive with caution"}:
            return "passable_with_conditions", "open_with_caution", category_raw
        if "local traffic only" in advice_l or "restricted access" in advice_l:
            return "passable_with_conditions", "restricted", category_raw

    # Vehicle/access restrictions are NOT full closures.
    # This must run before the generic flood/default-impassable logic because
    # QLD Traffic can combine generic flood safety advice with phrases like
    # "Restricted to four wheel drive vehicles only". Those should only block
    # the conservative all_blocking scenario, not impassable_only.
    explicit_full_closure = (
        "road closed" in text
        or "closed to all traffic" in text
        or "closed to all vehicles" in text
        or "no access" in text
        or "not passable" in text
        or "impassable" in text
        or "do not travel" in text
        or "do not proceed" in text
        or "emergency services only" in text
    )
    conditional_access = (
        "restricted to four wheel drive" in text
        or "four wheel drive vehicles only" in text
        or "4wd only" in text
        or "4 wd only" in text
        or "4x4 only" in text
        or "high clearance" in text
        or "local traffic only" in text
        or "restricted access" in text
    )
    if conditional_access and not explicit_full_closure:
        return "passable_with_conditions", "restricted", category_raw

    # Avoid treating a lane closure as a full road closure.
    if "lane closed" not in text and match_any(HARD_CLOSED_PATTERNS, text):
        return "impassable", "road_closed", category_raw

    if match_any(FLOOD_PATTERNS, text):
        # QLD Traffic often includes the generic safety advice
        # "Do not drive in flood waters" on events that are only lane-affected,
        # reduced, open with caution, or otherwise conditional. Do not treat that
        # generic advice as a full road closure unless the structured impact or
        # wording explicitly says the road is closed / not passable.
        impact_type_l = impact_type.lower()
        impact_subtype_l = impact_subtype.lower()
        explicit_flood_closure = (
            impact_type_l == "closures"
            or "road closed" in text
            or "closed to all traffic" in text
            or "closed to all vehicles" in text
            or "no access" in text
            or "not passable" in text
            or "impassable" in text
            or "do not travel" in text
            or "do not proceed" in text
            or "emergency services only" in text
        )
        clearly_conditional_flood = (
            impact_type_l == "lanes affected"
            or "lane" in impact_subtype_l
            or "all lanes affected" in impact_subtype_l
            or "lane or lanes reduced" in text
            or match_any(FLOOD_SOFTENERS, text)
            or match_any(SOFT_RESTRICT_PATTERNS, text)
        )
        if explicit_flood_closure:
            return "impassable", "road_closed", category_raw
        if clearly_conditional_flood:
            return "passable_with_conditions", "open_with_caution", category_raw
        # Flood present but no explicit closure. Keep it in the conservative
        # all_blocking scenario without elevating it to a full isolation closure.
        return "passable_with_conditions", "open_with_caution", category_raw

    # QLD Traffic often uses "All lanes affected" for a serious hazard, but that
    # does NOT by itself prove the road is closed. Treat it as conditional unless
    # the payload explicitly says the road is closed / not passable. This avoids
    # false isolation flags from "Changed traffic conditions" events.
    if impact_subtype.lower() == "all lanes affected":
        explicit_full_closure = (
            impact_type.lower() == "closures"
            or "road closed" in text
            or "closed to all traffic" in text
            or "no access" in text
            or "not passable" in text
            or "impassable" in text
            or "do not travel" in text
            or "do not proceed" in text
        )
        if explicit_full_closure:
            return "impassable", "road_closed", category_raw
        return "passable_with_conditions", "open_with_caution", category_raw

    if match_any(SOFT_RESTRICT_PATTERNS, text):
        if "local traffic only" in text or "restricted access" in text:
            return "passable_with_conditions", "restricted", category_raw
        return "passable_with_conditions", "open_with_caution", category_raw

    return "unknown", "other", category_raw


def reason_for(props: Dict[str, Any]) -> str:
    text = json.dumps(props, ensure_ascii=False, default=str).lower()
    if "flood" in text:
        return "flood"
    if "fire" in text:
        return "fire"
    if "crash" in text or "collision" in text:
        return "crash"
    if "landslide" in text:
        return "landslide"
    if "storm" in text or "fallen tree" in text:
        return "storm_damage"
    if "roadworks" in text or "planned" in text:
        return "maintenance"
    return "unknown"


def status_for(props: Dict[str, Any]) -> str:
    status = clean_str(props.get("status") or props.get("state")).lower()
    # Do not interpret "closed" as an ended event. In traffic feeds, closed can
    # describe the road state. Treat explicit cleared/resolved terms as ended.
    if status in {"ended", "cleared", "resolved", "inactive", "cancelled", "canceled"}:
        return "ended"
    if status in {"planned", "scheduled"}:
        return "scheduled"
    return "active"


def is_planned(props: Dict[str, Any]) -> bool:
    text = json.dumps(props, ensure_ascii=False, default=str).lower()
    return "roadworks" in text or "planned" in text


def normalise_raw_qld_feature(feature: Dict[str, Any], fetched_at: str, include_planned: bool) -> Optional[Closure]:
    props = feature.get("properties") or {}
    if is_planned(props) and not include_planned:
        return None

    geom_obj = geometry_from_jsonish(feature.get("geometry") or {"type": "Point", "coordinates": []})
    if geom_obj is None or geom_obj.is_empty:
        return None

    raw_fields = extract_raw_qld_fields(props)
    source_id = (
        raw_fields.get("source_event_id")
        or props.get("id")
        or props.get("event_id")
        or props.get("eventId")
        or props.get("guid")
        or props.get("reference")
        or props.get("url")
        or f"{props.get('title', '')}-{props.get('startTime', '')}-{props.get('lastUpdated', '')}"
    )
    passability, category, category_raw = classify_qld_event(props)

    impact = props.get("impact") if isinstance(props.get("impact"), dict) else {}
    advice = best_nonempty(raw_fields.get("raw_advice"), props.get("advice"))
    impact_subtype = best_nonempty(raw_fields.get("raw_impact_subtype"), impact.get("impact_subtype"))
    description = best_nonempty(raw_fields.get("raw_description"), props.get("description"), advice)
    if impact_subtype and impact_subtype.lower() not in description.lower():
        description = f"{description} | {impact_subtype}" if description else impact_subtype

    return Closure(
        event_id=stable_id(str(source_id)),
        source="qldtraffic",
        jurisdiction="qld",
        category_raw=category_raw,
        category_norm=category,
        passability_norm=passability,
        status_norm=status_for(props),
        reason_norm=reason_for(props),
        start_time=clean_str(props.get("startTime") or props.get("start_time") or props.get("fromDate") or props.get("from")),
        end_time=clean_str(props.get("endTime") or props.get("end_time") or props.get("toDate") or props.get("to")),
        last_updated=clean_str(props.get("lastUpdated") or props.get("updated") or props.get("last_update")),
        fetched_at=fetched_at,
        title=best_nonempty(raw_fields.get("raw_title"), props.get("headline"), props.get("title")),
        description=description,
        road_name=best_nonempty(raw_fields.get("raw_road"), props.get("road"), props.get("road_name"), props.get("roadName")),
        locality=best_nonempty(raw_fields.get("raw_locality"), props.get("locality"), props.get("suburb")),
        direction=clean_str(props.get("direction")),
        lanes_affected=clean_str(props.get("lanes") or props.get("lanes_affected")),
        restrictions_text=best_nonempty(props.get("restrictions"), raw_fields.get("raw_advice"), advice),
        url=best_nonempty(props.get("url"), props.get("web_url"), f"https://api.qldtraffic.qld.gov.au/v2/events/{source_id}" if source_id else ""),
        source_event_id=clean_str(source_id),
        raw_title=raw_fields.get("raw_title", ""),
        raw_description=raw_fields.get("raw_description", ""),
        raw_advice=raw_fields.get("raw_advice", ""),
        raw_event_type=raw_fields.get("raw_event_type", ""),
        raw_event_subtype=raw_fields.get("raw_event_subtype", ""),
        raw_impact_type=raw_fields.get("raw_impact_type", ""),
        raw_impact_subtype=raw_fields.get("raw_impact_subtype", ""),
        raw_road=raw_fields.get("raw_road", ""),
        raw_locality=raw_fields.get("raw_locality", ""),
        raw_status=raw_fields.get("raw_status", ""),
        geometry=geom_obj,
        raw_properties=props,
    )


def closure_from_normalised_feature(feature: Dict[str, Any], fetched_at: str, include_planned: bool) -> Optional[Closure]:
    props = feature.get("properties") or {}
    geom_obj = geometry_from_jsonish(feature.get("geometry"))
    if geom_obj is None or geom_obj.is_empty:
        return None

    category_norm = clean_str(props.get("category_norm")) or "other"
    passability_norm = clean_str(props.get("passability_norm")) or "unknown"
    status_norm = clean_str(props.get("status_norm")) or "active"
    reason_norm = clean_str(props.get("reason_norm")) or "unknown"

    if reason_norm == "maintenance" and not include_planned:
        return None

    source_id = clean_str(props.get("event_id") or props.get("source_id") or props.get("id") or props.get("title"))
    return Closure(
        event_id=source_id or stable_id(json.dumps(feature, sort_keys=True, default=str)[:500]),
        source=clean_str(props.get("source")) or "qldtraffic",
        jurisdiction=clean_str(props.get("jurisdiction")) or "qld",
        category_raw=clean_str(props.get("category_raw")),
        category_norm=category_norm,
        passability_norm=passability_norm,
        status_norm=status_norm,
        reason_norm=reason_norm,
        start_time=clean_str(props.get("start_time")),
        end_time=clean_str(props.get("end_time")),
        last_updated=clean_str(props.get("last_updated")),
        fetched_at=clean_str(props.get("fetched_at")) or fetched_at,
        title=clean_str(props.get("title")),
        description=clean_str(props.get("description")),
        road_name=clean_str(props.get("road_name")),
        locality=clean_str(props.get("locality")),
        direction=clean_str(props.get("direction")),
        lanes_affected=clean_str(props.get("lanes_affected")),
        restrictions_text=clean_str(props.get("restrictions_text")),
        url=clean_str(props.get("url")),
        source_event_id=clean_str(props.get("source_event_id") or props.get("source_id") or props.get("id")),
        raw_title=clean_str(props.get("raw_title")),
        raw_description=clean_str(props.get("raw_description")),
        raw_advice=clean_str(props.get("raw_advice")),
        raw_event_type=clean_str(props.get("raw_event_type")),
        raw_event_subtype=clean_str(props.get("raw_event_subtype")),
        raw_impact_type=clean_str(props.get("raw_impact_type")),
        raw_impact_subtype=clean_str(props.get("raw_impact_subtype")),
        raw_road=clean_str(props.get("raw_road")),
        raw_locality=clean_str(props.get("raw_locality")),
        raw_status=clean_str(props.get("raw_status")),
        geometry=geom_obj,
        raw_properties=props,
    )


def load_closures_from_geojson(path: Path, include_planned: bool) -> Tuple[List[Closure], Dict[str, Any]]:
    fetched_at = utc_now_iso()
    payload = json.loads(path.read_text(encoding="utf-8"))
    features = payload.get("features") or []
    closures: List[Closure] = []
    errors: List[str] = []

    for feature in features:
        try:
            props = feature.get("properties") or {}
            if "passability_norm" in props or "category_norm" in props:
                c = closure_from_normalised_feature(feature, fetched_at, include_planned=include_planned)
            else:
                c = normalise_raw_qld_feature(feature, fetched_at, include_planned=include_planned)
            if c is not None:
                closures.append(c)
        except Exception as exc:
            errors.append(repr(exc))

    meta = {
        "source_mode": "geojson_file",
        "source_path": str(path),
        "raw_count": len(features),
        "normalised_count": len(closures),
        "errors": errors[:50],
    }
    return closures, meta


def load_closures_from_csv(path: Path, include_planned: bool) -> Tuple[List[Closure], Dict[str, Any]]:
    fetched_at = utc_now_iso()
    closures: List[Closure] = []
    errors: List[str] = []
    raw_count = 0
    with path.open(encoding="utf-8", newline="") as handle:
        for row in csv.DictReader(handle):
            raw_count += 1
            try:
                geom_obj = geometry_from_jsonish(row.get("geometry_json") or row.get("geometry"))
                if geom_obj is None or geom_obj.is_empty:
                    continue
                reason_norm = clean_str(row.get("reason_norm")) or "unknown"
                if reason_norm == "maintenance" and not include_planned:
                    continue
                closures.append(
                    Closure(
                        event_id=clean_str(row.get("event_id")) or stable_id(str(raw_count)),
                        source=clean_str(row.get("source")) or "qldtraffic",
                        jurisdiction=clean_str(row.get("jurisdiction")) or "qld",
                        category_raw=clean_str(row.get("category_raw")),
                        category_norm=clean_str(row.get("category_norm")) or "other",
                        passability_norm=clean_str(row.get("passability_norm")) or "unknown",
                        status_norm=clean_str(row.get("status_norm")) or "active",
                        reason_norm=reason_norm,
                        start_time=clean_str(row.get("start_time")),
                        end_time=clean_str(row.get("end_time")),
                        last_updated=clean_str(row.get("last_updated")),
                        fetched_at=clean_str(row.get("fetched_at")) or fetched_at,
                        title=clean_str(row.get("title")),
                        description=clean_str(row.get("description")),
                        road_name=clean_str(row.get("road_name")),
                        locality=clean_str(row.get("locality")),
                        direction=clean_str(row.get("direction")),
                        lanes_affected=clean_str(row.get("lanes_affected")),
                        restrictions_text=clean_str(row.get("restrictions_text")),
                        url=clean_str(row.get("url")),
                        source_event_id=clean_str(row.get("source_event_id")),
                        raw_title=clean_str(row.get("raw_title")),
                        raw_description=clean_str(row.get("raw_description")),
                        raw_advice=clean_str(row.get("raw_advice")),
                        raw_event_type=clean_str(row.get("raw_event_type")),
                        raw_event_subtype=clean_str(row.get("raw_event_subtype")),
                        raw_impact_type=clean_str(row.get("raw_impact_type")),
                        raw_impact_subtype=clean_str(row.get("raw_impact_subtype")),
                        raw_road=clean_str(row.get("raw_road")),
                        raw_locality=clean_str(row.get("raw_locality")),
                        raw_status=clean_str(row.get("raw_status")),
                        geometry=geom_obj,
                        raw_properties=dict(row),
                    )
                )
            except Exception as exc:
                errors.append(repr(exc))

    meta = {
        "source_mode": "csv_file",
        "source_path": str(path),
        "raw_count": raw_count,
        "normalised_count": len(closures),
        "errors": errors[:50],
    }
    return closures, meta


def fetch_qld_closures(include_planned: bool, timeout_s: float = 30.0) -> Tuple[List[Closure], Dict[str, Any]]:
    fetched_at = utc_now_iso()
    response = requests.get(QLD_TRAFFIC_URL, timeout=timeout_s, headers={"User-Agent": "qld-isolation-proper/1.0"})
    response.raise_for_status()
    payload = response.json()
    features = payload.get("features") or []

    closures: List[Closure] = []
    skipped_planned = 0
    errors: List[str] = []
    for feature in features:
        try:
            props = feature.get("properties") or {}
            if is_planned(props) and not include_planned:
                skipped_planned += 1
                continue
            c = normalise_raw_qld_feature(feature, fetched_at, include_planned=include_planned)
            if c is not None:
                closures.append(c)
        except Exception as exc:
            errors.append(repr(exc))

    meta = {
        "source_mode": "live_qldtraffic",
        "url": QLD_TRAFFIC_URL,
        "http_status": response.status_code,
        "fetched_at": fetched_at,
        "raw_count": len(features),
        "normalised_count": len(closures),
        "skipped_planned": skipped_planned,
        "errors": errors[:50],
    }
    return closures, meta


# ---------------------------------------------------------------------
# Places and hubs
# ---------------------------------------------------------------------

def first_value(row: Dict[str, Any], keys: Sequence[str]) -> str:
    for key in keys:
        val = row.get(key)
        if val not in (None, ""):
            return clean_str(val)
    return ""


def load_places(path: Path, qld_only: bool = True) -> List[Place]:
    if not path.exists():
        raise FileNotFoundError(f"Places CSV not found: {path}")

    out: List[Place] = []
    with path.open(encoding="utf-8-sig", newline="") as handle:
        reader = csv.DictReader(handle)
        for idx, row in enumerate(reader, start=1):
            lat_s = first_value(row, ["lat", "latitude", "Latitude", "LATITUDE", "y", "Y"])
            lon_s = first_value(row, ["lon", "lng", "longitude", "Longitude", "LONGITUDE", "x", "X"])
            try:
                lat = float(lat_s)
                lon = float(lon_s)
            except Exception:
                continue
            if qld_only and not in_qld_bbox(lat, lon):
                continue

            name = first_value(row, ["name", "place_name", "Place_Name", "NAME", "gazetteer_name"])
            if not name:
                name = f"place_{idx}"

            place_id = first_value(row, ["place_id", "id", "gazetteer_id", "feature_id", "ref"])
            if not place_id:
                place_id = stable_id(f"place:{name}:{lat:.6f}:{lon:.6f}")

            is_hub_s = first_value(row, ["is_hub", "hub", "anchor", "is_anchor"])
            is_hub = is_hub_s.lower() in YES_VALUES

            out.append(
                Place(
                    place_id=place_id,
                    name=name,
                    lat=lat,
                    lon=lon,
                    is_hub=is_hub,
                    state=first_value(row, ["state", "jurisdiction"]) or "qld",
                    lga=first_value(row, ["lga", "LGA", "local_government_area"]),
                    place_type=first_value(row, ["place_type", "type", "feature_type", "class"]),
                    raw=dict(row),
                )
            )
    return out


# ---------------------------------------------------------------------
# Graph loading, geometry parsing, and spatial indexes
# ---------------------------------------------------------------------

def load_graph(path: Path) -> nx.Graph:
    if not path.exists():
        raise FileNotFoundError(f"GraphML not found: {path}")
    print(f"[LOAD] graph: {path}")
    G = nx.read_graphml(path)
    if G.number_of_nodes() == 0 or G.number_of_edges() == 0:
        raise RuntimeError(f"Graph appears empty: nodes={G.number_of_nodes()} edges={G.number_of_edges()}")
    print(f"[GRAPH] nodes={G.number_of_nodes():,} edges={G.number_of_edges():,} directed={G.is_directed()} multi={G.is_multigraph()}")
    return G



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


def apply_manual_connectors(G: nx.Graph, path: Path) -> int:
    """Add small audited connector edges for known graph topology defects.

    This is intended for short, explicit graph repairs such as a snapped road
    component being separated from the main component by a tiny topology gap.
    It does not change closure classification; it only repairs base graph
    connectivity before reachability is calculated.
    """
    if not path or str(path).strip() == "":
        return 0
    if not path.exists():
        print(f"[MANUAL] connector file not found, skipping: {path}")
        return 0

    added = 0
    with path.open(encoding="utf-8-sig", newline="") as handle:
        reader = csv.DictReader(handle)
        for idx, row in enumerate(reader, start=1):
            u = clean_str(row.get("from_node") or row.get("u"))
            v = clean_str(row.get("to_node") or row.get("v"))

            try:
                from_lon = float(row.get("from_lon") or (G.nodes[u].get("x") if u in G else ""))
                from_lat = float(row.get("from_lat") or (G.nodes[u].get("y") if u in G else ""))
                to_lon = float(row.get("to_lon") or (G.nodes[v].get("x") if v in G else ""))
                to_lat = float(row.get("to_lat") or (G.nodes[v].get("y") if v in G else ""))
            except Exception:
                print(f"[MANUAL] row {idx}: could not determine connector coordinates, skipped")
                continue

            if not u:
                u = nearest_graph_node_id(G, from_lat, from_lon)
                print(f"[MANUAL] row {idx}: snapped from coordinate to node {u}")
            if not v:
                v = nearest_graph_node_id(G, to_lat, to_lon)
                print(f"[MANUAL] row {idx}: snapped to coordinate to node {v}")
            if u not in G:
                print(f"[MANUAL] row {idx}: from_node not in graph: {u}")
                continue
            if v not in G:
                print(f"[MANUAL] row {idx}: to_node not in graph: {v}")
                continue

            try:
                length_m = float(row.get("length_m") or haversine_m(from_lat, from_lon, to_lat, to_lon))
            except Exception:
                length_m = haversine_m(from_lat, from_lon, to_lat, to_lon)

            reason = clean_str(row.get("reason")) or "manual graph topology repair"
            name = clean_str(row.get("name")) or "manual_graph_connector"
            geometry_wkt = LineString([(from_lon, from_lat), (to_lon, to_lat)]).wkt

            attrs = {
                "geometry": geometry_wkt,
                "length": float(length_m),
                "name": name,
                "highway": "manual_connector",
                "manual_connector": "true",
                "manual_reason": reason,
                "manual_source": clean_str(row.get("source")) or "manual_graph_connectors.csv",
            }

            if G.is_multigraph():
                key_fwd = clean_str(row.get("key_fwd")) or f"manual_connector_{idx}_fwd"
                G.add_edge(u, v, key=key_fwd, **attrs)
                added += 1
                if G.is_directed():
                    key_rev = clean_str(row.get("key_rev")) or f"manual_connector_{idx}_rev"
                    G.add_edge(v, u, key=key_rev, **attrs)
                    added += 1
            else:
                G.add_edge(u, v, **attrs)
                added += 1
                if G.is_directed():
                    G.add_edge(v, u, **attrs)
                    added += 1

            print(f"[MANUAL] added connector {u} <-> {v} length={length_m:.1f}m reason={reason}")

    print(f"[MANUAL] connectors added as graph edges: {added}")
    return added


def node_lonlat(G: nx.Graph, node: Any) -> Optional[Tuple[float, float]]:
    data = G.nodes[node]
    try:
        return float(data["x"]), float(data["y"])
    except Exception:
        return None


def edge_road_name(data: Dict[str, Any]) -> str:
    name = data.get("name") or data.get("ref") or ""
    if isinstance(name, (list, tuple, set)):
        return " / ".join(clean_str(v) for v in name if clean_str(v))
    return clean_str(name)


def normalise_road_name(value: Any) -> str:
    text = clean_str(value).lower()
    text = re.sub(r"\([^)]*\)", " ", text)
    text = re.sub(r"[^a-z0-9]+", " ", text)
    return re.sub(r"\s+", " ", text).strip()


def road_name_variants(value: Any) -> set[str]:
    text = clean_str(value)
    if not text:
        return set()
    parts = re.split(r"\s*/\s*|\s*;\s*", text)
    out: set[str] = set()
    for part in parts + [text]:
        norm = normalise_road_name(part)
        if not norm or norm in {"unnamed road", "unknown"}:
            continue
        out.add(norm)
    return out


def road_names_match(edge_name: str, closure_names: set[str]) -> bool:
    if not closure_names:
        return True
    edge_norm = normalise_road_name(edge_name)
    if not edge_norm:
        return False
    return any(name == edge_norm or name in edge_norm or edge_norm in name for name in closure_names)


def parse_edge_geometry(G: nx.Graph, u: Any, v: Any, data: Dict[str, Any]) -> Optional[Any]:
    geom_val = data.get("geometry")
    geom = None
    if geom_val not in (None, ""):
        if isinstance(geom_val, (LineString, MultiLineString)):
            geom = geom_val
        elif isinstance(geom_val, str):
            try:
                geom = wkt.loads(geom_val)
            except Exception:
                try:
                    geom = shape(json.loads(geom_val))
                except Exception:
                    geom = None
    if geom is None:
        a = node_lonlat(G, u)
        b = node_lonlat(G, v)
        if a is None or b is None:
            return None
        geom = LineString([a, b])
    if geom.is_empty:
        return None
    return geom


def iter_graph_edges(G: nx.Graph) -> Iterable[Tuple[Any, Any, Any, Dict[str, Any]]]:
    if G.is_multigraph():
        for u, v, k, data in G.edges(keys=True, data=True):
            yield u, v, k, data
    else:
        for u, v, data in G.edges(data=True):
            yield u, v, 0, data


def build_edge_index(G: nx.Graph) -> EdgeIndex:
    print("[INDEX] building edge spatial index in EPSG:3857")
    t0 = time.perf_counter()
    edge_refs: List[EdgeRef] = []
    edge_geoms_m: List[Any] = []
    edge_names: List[str] = []
    wkb_to_indices: Dict[bytes, List[int]] = {}

    bad = 0
    for u, v, k, data in iter_graph_edges(G):
        try:
            geom = parse_edge_geometry(G, u, v, data)
            if geom is None:
                bad += 1
                continue
            geom_m = geom_to_m(geom)
            if geom_m.is_empty:
                bad += 1
                continue
            idx = len(edge_refs)
            edge_refs.append(EdgeRef(u, v, k))
            edge_geoms_m.append(geom_m)
            edge_names.append(edge_road_name(data))
            wkb_to_indices.setdefault(geom_m.wkb, []).append(idx)
        except Exception:
            bad += 1

    if not edge_refs:
        raise RuntimeError("Could not build any road-edge geometries from the graph.")

    tree = STRtree(edge_geoms_m)
    print(f"[INDEX] edges indexed={len(edge_refs):,} skipped={bad:,} elapsed={time.perf_counter() - t0:.1f}s")
    return EdgeIndex(edge_refs=edge_refs, edge_geoms_m=edge_geoms_m, edge_names=edge_names, tree=tree, wkb_to_indices=wkb_to_indices)


def strtree_indices(edge_index: EdgeIndex, query_geom: Any) -> Iterable[int]:
    hits = edge_index.tree.query(query_geom)
    for hit in hits:
        if isinstance(hit, numbers.Integral):
            idx = int(hit)
            if 0 <= idx < len(edge_index.edge_refs):
                yield idx
        else:
            # Shapely 1.x returns geometries. Duplicates are possible, so use all
            # indices that share the same WKB.
            for idx in edge_index.wkb_to_indices.get(hit.wkb, []):
                yield idx


def build_node_index(G: nx.Graph) -> NodeIndex:
    print("[INDEX] building node nearest-neighbour index")
    node_ids: List[Any] = []
    xy_m: List[Tuple[float, float]] = []
    for node, data in G.nodes(data=True):
        try:
            lon = float(data["x"])
            lat = float(data["y"])
        except Exception:
            continue
        x, y = point_wgs_to_m(lon, lat)
        node_ids.append(node)
        xy_m.append((x, y))

    if not node_ids:
        raise RuntimeError("Could not build node index; graph nodes have no x/y coordinates.")

    tree = None
    try:
        from scipy.spatial import cKDTree  # type: ignore

        tree = cKDTree(xy_m)
        print(f"[INDEX] nodes indexed={len(node_ids):,} using scipy cKDTree")
    except Exception:
        print(f"[INDEX] nodes indexed={len(node_ids):,}; scipy unavailable, using slower fallback")

    return NodeIndex(node_ids=node_ids, xy_m=xy_m, tree=tree)


def nearest_node(node_index: NodeIndex, lat: float, lon: float, max_dist_m: Optional[float]) -> Tuple[Optional[Any], Optional[float]]:
    qx, qy = point_wgs_to_m(lon, lat)
    if node_index.tree is not None:
        dist, idx = node_index.tree.query([(qx, qy)], k=1)
        d = float(dist[0])
        i = int(idx[0])
        if max_dist_m is not None and d > max_dist_m:
            return None, d
        return node_index.node_ids[i], d

    best_i = -1
    best_d2 = float("inf")
    for i, (x, y) in enumerate(node_index.xy_m):
        dx = x - qx
        dy = y - qy
        d2 = dx * dx + dy * dy
        if d2 < best_d2:
            best_i = i
            best_d2 = d2
    if best_i < 0:
        return None, None
    d = math.sqrt(best_d2)
    if max_dist_m is not None and d > max_dist_m:
        return None, d
    return node_index.node_ids[best_i], d


def nearby_nodes(
    node_index: NodeIndex,
    lat: float,
    lon: float,
    *,
    max_dist_m: float,
    k_nearest: int,
) -> List[Tuple[Any, float]]:
    """Return nearby graph nodes ordered by projected distance from a place."""
    if k_nearest <= 0:
        return []

    qx, qy = point_wgs_to_m(lon, lat)
    if node_index.tree is not None:
        k = min(k_nearest, len(node_index.node_ids))
        dist, idx = node_index.tree.query([(qx, qy)], k=k)
        distances = dist[0]
        indices = idx[0]
        if k == 1:
            distances = [float(distances)]
            indices = [int(indices)]

        out: List[Tuple[Any, float]] = []
        for d_raw, i_raw in zip(distances, indices):
            d = float(d_raw)
            i = int(i_raw)
            if not math.isfinite(d) or i < 0 or i >= len(node_index.node_ids):
                continue
            if d > max_dist_m:
                continue
            out.append((node_index.node_ids[i], d))
        return out

    ranked: List[Tuple[float, int]] = []
    max_d2 = max_dist_m * max_dist_m
    for i, (x, y) in enumerate(node_index.xy_m):
        dx = x - qx
        dy = y - qy
        d2 = dx * dx + dy * dy
        if d2 <= max_d2:
            ranked.append((d2, i))
    ranked.sort(key=lambda x: x[0])
    return [(node_index.node_ids[i], math.sqrt(d2)) for d2, i in ranked[:k_nearest]]



def graph_edge_length_m(G: nx.Graph, u: Any, v: Any, data: Dict[str, Any]) -> float:
    for key in ("length", "length_m", "distance", "distance_m"):
        try:
            value = data.get(key)
            if value not in (None, ""):
                length = float(value)
                if math.isfinite(length) and length > 0:
                    return length
        except Exception:
            pass
    geom = parse_edge_geometry(G, u, v, data)
    if geom is not None and not geom.is_empty:
        try:
            return float(geom_to_m(geom).length)
        except Exception:
            pass
    a = node_lonlat(G, u)
    b = node_lonlat(G, v)
    if a is not None and b is not None:
        return haversine_m(a[1], a[0], b[1], b[0])
    return 1.0


def edge_records_between(G: nx.Graph, u: Any, v: Any) -> List[Tuple[Any, Dict[str, Any]]]:
    if G.is_multigraph():
        try:
            edge_data = G.get_edge_data(u, v) or {}
            return [(k, data) for k, data in edge_data.items()]
        except Exception:
            return []
    data = G.get_edge_data(u, v)
    return [(0, data)] if data else []


def shortest_hub_route(
    G: nx.Graph,
    start: Any,
    hub_node_names: Dict[Any, str],
    *,
    blocked_edges: Optional[set[Tuple[Any, Any, Any]]] = None,
    max_points: int = 1200,
) -> Dict[str, Any]:
    """Return a shortest currently-open route from a place node to the nearest hub node."""
    if start is None or start not in G or not hub_node_names:
        return {}

    targets = set(hub_node_names)
    blocked = blocked_edges or set()
    route_counter = 0
    queue: List[Tuple[float, int, Any]] = [(0.0, route_counter, start)]
    dist: Dict[Any, float] = {start: 0.0}
    prev: Dict[Any, Tuple[Any, Any, Dict[str, Any]]] = {}
    seen: set[Any] = set()
    end = None

    while queue:
        cost, _order, node = heapq.heappop(queue)
        if node in seen:
            continue
        seen.add(node)
        if node in targets:
            end = node
            break
        for neighbour, edge in iter_adjacent_edges(G, node):
            if neighbour in seen:
                continue
            candidates = edge_records_between(G, edge[0], edge[1]) or edge_records_between(G, edge[1], edge[0])
            candidates = [(key, data) for key, data in candidates if not is_edge_blocked((edge[0], edge[1], key), blocked)]
            if not candidates:
                continue
            key, data = min(candidates, key=lambda item: graph_edge_length_m(G, edge[0], edge[1], item[1]))
            step = graph_edge_length_m(G, edge[0], edge[1], data)
            new_cost = cost + step
            if new_cost < dist.get(neighbour, float("inf")):
                dist[neighbour] = new_cost
                prev[neighbour] = (node, key, data)
                route_counter += 1
                heapq.heappush(queue, (new_cost, route_counter, neighbour))

    if end is None or end == start:
        return {}

    pieces: List[List[Tuple[float, float]]] = []
    node = end
    while node != start:
        prior, _key, data = prev[node]
        geom = parse_edge_geometry(G, prior, node, data)
        if geom is not None and not geom.is_empty:
            if isinstance(geom, MultiLineString):
                coords = list(max(geom.geoms, key=lambda g: g.length).coords)
            else:
                coords = list(geom.coords)
            a = node_lonlat(G, prior)
            b = node_lonlat(G, node)
            if a is not None and b is not None and coords:
                if haversine_m(a[1], a[0], coords[0][1], coords[0][0]) > haversine_m(a[1], a[0], coords[-1][1], coords[-1][0]):
                    coords = list(reversed(coords))
            pieces.append([(float(x), float(y)) for x, y in coords])
        else:
            a = node_lonlat(G, prior)
            b = node_lonlat(G, node)
            if a is not None and b is not None:
                pieces.append([a, b])
        node = prior

    coords_out: List[Tuple[float, float]] = []
    for coords in reversed(pieces):
        if coords_out and coords and coords_out[-1] == coords[0]:
            coords_out.extend(coords[1:])
        else:
            coords_out.extend(coords)
    if len(coords_out) > max_points:
        step = max(1, math.ceil(len(coords_out) / max_points))
        coords_out = coords_out[::step] + ([coords_out[-1]] if coords_out[-1] != coords_out[::step][-1] else [])

    return {
        "hub_name": hub_node_names.get(end, str(end)),
        "distance_m": dist[end],
        "geometry": {"type": "LineString", "coordinates": coords_out},
    }


def build_route_geometry_from_next_hops(
    G: nx.Graph,
    start: Any,
    end: Any,
    next_hop: Dict[Any, Tuple[Any, Any, Dict[str, Any]]],
    *,
    max_points: int = 1200,
) -> Dict[str, Any]:
    """Reconstruct route geometry from a node-to-hub next-hop table."""
    if start is None or end is None or start == end:
        return {}

    pieces: List[List[Tuple[float, float]]] = []
    node = start
    seen: set[Any] = set()

    while node != end:
        if node in seen:
            return {}
        seen.add(node)
        hop = next_hop.get(node)
        if hop is None:
            return {}
        neighbour, _key, data = hop
        geom = parse_edge_geometry(G, node, neighbour, data)
        if geom is not None and not geom.is_empty:
            if isinstance(geom, MultiLineString):
                coords = list(max(geom.geoms, key=lambda g: g.length).coords)
            else:
                coords = list(geom.coords)
            a = node_lonlat(G, node)
            b = node_lonlat(G, neighbour)
            if a is not None and b is not None and coords:
                if haversine_m(a[1], a[0], coords[0][1], coords[0][0]) > haversine_m(a[1], a[0], coords[-1][1], coords[-1][0]):
                    coords = list(reversed(coords))
            pieces.append([(float(x), float(y)) for x, y in coords])
        else:
            a = node_lonlat(G, node)
            b = node_lonlat(G, neighbour)
            if a is not None and b is not None:
                pieces.append([a, b])
        node = neighbour

    coords_out: List[Tuple[float, float]] = []
    for coords in pieces:
        if coords_out and coords and coords_out[-1] == coords[0]:
            coords_out.extend(coords[1:])
        else:
            coords_out.extend(coords)
    if len(coords_out) > max_points:
        step = max(1, math.ceil(len(coords_out) / max_points))
        coords_out = coords_out[::step] + ([coords_out[-1]] if coords_out[-1] != coords_out[::step][-1] else [])
    return {"type": "LineString", "coordinates": coords_out} if coords_out else {}


def multi_source_hub_routes(
    G: nx.Graph,
    hub_node_names: Dict[Any, str],
    blocked_edges: set[Tuple[Any, Any, Any]],
) -> Tuple[Dict[Any, float], Dict[Any, Any], Dict[Any, Tuple[Any, Any, Dict[str, Any]]]]:
    """Return nearest-hub distances and next hops for all nodes in one Dijkstra pass."""
    blocked = blocked_edges or set()
    route_counter = 0
    queue: List[Tuple[float, int, Any, Any]] = []
    dist: Dict[Any, float] = {}
    nearest_hub: Dict[Any, Any] = {}
    next_hop: Dict[Any, Tuple[Any, Any, Dict[str, Any]]] = {}

    for hub_node in hub_node_names:
        if hub_node is None or hub_node not in G or hub_node in dist:
            continue
        dist[hub_node] = 0.0
        nearest_hub[hub_node] = hub_node
        heapq.heappush(queue, (0.0, route_counter, hub_node, hub_node))
        route_counter += 1

    seen: set[Any] = set()
    while queue:
        cost, _order, node, hub_node = heapq.heappop(queue)
        if node in seen:
            continue
        seen.add(node)

        for neighbour, edge in iter_adjacent_edges(G, node):
            if neighbour in seen:
                continue
            candidates = edge_records_between(G, edge[0], edge[1]) or edge_records_between(G, edge[1], edge[0])
            candidates = [(key, data) for key, data in candidates if not is_edge_blocked((edge[0], edge[1], key), blocked)]
            if not candidates:
                continue
            key, data = min(candidates, key=lambda item: graph_edge_length_m(G, edge[0], edge[1], item[1]))
            step = graph_edge_length_m(G, edge[0], edge[1], data)
            new_cost = cost + step
            if new_cost < dist.get(neighbour, float("inf")):
                dist[neighbour] = new_cost
                nearest_hub[neighbour] = hub_node
                next_hop[neighbour] = (node, key, data)
                route_counter += 1
                heapq.heappush(queue, (new_cost, route_counter, neighbour, hub_node))

    return dist, nearest_hub, next_hop


def build_hub_access_routes(
    G: nx.Graph,
    places: Sequence[Place],
    place_nodes: Dict[str, Any],
    hub_nodes_by_place_id: Dict[str, Any],
    place_rows: Sequence[Dict[str, Any]],
    blocked_edges: set[Tuple[Any, Any, Any]],
) -> Dict[str, Dict[str, Any]]:
    hub_node_names: Dict[Any, str] = {}
    place_by_id = {p.place_id: p for p in places}
    for place_id, node in hub_nodes_by_place_id.items():
        if node is None:
            continue
        hub_place = place_by_id.get(place_id)
        hub_node_names.setdefault(node, hub_place.name if hub_place else str(place_id))
    hub_distances, nearest_hubs, next_hop = multi_source_hub_routes(G, hub_node_names, blocked_edges)
    routes: Dict[str, Dict[str, Any]] = {}
    for row in place_rows:
        if row.get("isolation_category") != "not_isolated" or str(row.get("is_hub", "")).strip().lower() in YES_VALUES:
            continue
        place_id = str(row.get("place_id") or "")
        start = place_nodes.get(place_id)
        hub_node = nearest_hubs.get(start)
        if start is None or hub_node is None or start == hub_node:
            continue
        geometry = build_route_geometry_from_next_hops(G, start, hub_node, next_hop)
        if geometry:
            routes[place_id] = {
                "hub_name": hub_node_names.get(hub_node, str(hub_node)),
                "distance_m": hub_distances.get(start, 0.0),
                "geometry": geometry,
            }
    return routes

# ---------------------------------------------------------------------
# Closure blocking logic
# ---------------------------------------------------------------------

def is_active_closure(c: Closure) -> bool:
    return (c.status_norm or "active").lower() not in {"ended", "cleared", "resolved", "inactive", "cancelled", "canceled"}


def is_impassable_blocking(c: Closure) -> bool:
    if not is_active_closure(c):
        return False
    return c.category_norm in {"road_closed", "restricted"} and c.passability_norm == "impassable"


def is_all_blocking(c: Closure) -> bool:
    if not is_active_closure(c):
        return False
    if c.category_norm in {"road_closed", "restricted"} and c.passability_norm in {"impassable", "passable_with_conditions"}:
        return True
    if c.category_norm == "other" and c.passability_norm in {"", "unknown"}:
        text = f"{c.title} {c.description} {c.restrictions_text}".lower()
        phrases = (
            "road closed",
            "road closure",
            "closed to all vehicles",
            "no access",
            "do not drive in flood waters",
            "do not travel",
            "use alternative route",
            "use an alternative route",
        )
        return any(p in text for p in phrases)
    return False


def confidence_for_distance(distance_m: Optional[float], high_m: float = 75.0, medium_m: float = 200.0) -> str:
    if distance_m is None:
        return "unmatched"
    if distance_m <= high_m:
        return "high"
    if distance_m <= medium_m:
        return "medium"
    return "low"


def closure_match_base_row(scenario: str, c: Closure) -> Dict[str, Any]:
    return {
        "scenario": scenario,
        "closure_id": c.event_id,
        "source": c.source,
        "category_norm": c.category_norm,
        "passability_norm": c.passability_norm,
        "status_norm": c.status_norm,
        "reason_norm": c.reason_norm,
        "title": c.title,
        "road_name": c.road_name,
        "locality": c.locality,
        "description": c.description,
        "restrictions_text": c.restrictions_text,
        "source_event_id": c.source_event_id,
        "raw_advice": c.raw_advice,
        "raw_event_type": c.raw_event_type,
        "raw_event_subtype": c.raw_event_subtype,
        "raw_impact_type": c.raw_impact_type,
        "raw_impact_subtype": c.raw_impact_subtype,
        "raw_properties_json": json.dumps(c.raw_properties or {}, ensure_ascii=False, default=str),
        "geometry_type": c.geometry_type,
        "url": c.url,
    }


def _iter_line_parts_only(geom: Any) -> Iterable[Any]:
    """Yield line components from an arbitrary shapely geometry."""
    if geom is None or geom.is_empty:
        return
    if isinstance(geom, LineString):
        yield geom
    elif isinstance(geom, MultiLineString):
        for g in geom.geoms:
            if g is not None and not g.is_empty:
                yield g
    elif isinstance(geom, GeometryCollection):
        for g in geom.geoms:
            yield from _iter_line_parts_only(g)


def _angle_degrees_between_points(a: Any, b: Any) -> Optional[float]:
    try:
        dx = float(b.x) - float(a.x)
        dy = float(b.y) - float(a.y)
    except Exception:
        return None
    if abs(dx) < 1e-9 and abs(dy) < 1e-9:
        return None
    return math.degrees(math.atan2(dy, dx))


def _line_angle_degrees(line: Any) -> Optional[float]:
    if line is None or line.is_empty or getattr(line, "length", 0.0) <= 0:
        return None
    try:
        a = line.interpolate(0.0)
        b = line.interpolate(float(line.length))
        return _angle_degrees_between_points(a, b)
    except Exception:
        return None


def _line_angle_at_projection(line: Any, projection_m: float, window_m: float) -> Optional[float]:
    if line is None or line.is_empty or getattr(line, "length", 0.0) <= 0:
        return None
    length = float(line.length)
    window = max(1.0, min(float(window_m), max(1.0, length / 2.0)))
    a_m = max(0.0, projection_m - window)
    b_m = min(length, projection_m + window)
    if b_m - a_m < 1.0:
        a_m = max(0.0, projection_m - 1.0)
        b_m = min(length, projection_m + 1.0)
    if b_m <= a_m:
        return None
    try:
        a = line.interpolate(a_m)
        b = line.interpolate(b_m)
        return _angle_degrees_between_points(a, b)
    except Exception:
        return None


def _angle_difference_180(a: Optional[float], b: Optional[float]) -> Optional[float]:
    if a is None or b is None:
        return None
    diff = abs((a - b) % 180.0)
    return min(diff, 180.0 - diff)


def _flat_buffer(geom: Any, distance_m: float) -> Any:
    """Buffer linework without round end caps so endpoint spill is not enlarged."""
    if distance_m <= 0:
        return geom
    try:
        return geom.buffer(distance_m, cap_style=2)
    except TypeError:
        # Very old Shapely fallback. This may use round caps, but the projection
        # span checks below still reject endpoint-only/cross-road matches.
        return geom.buffer(distance_m)


def _line_overlap_metrics(
    edge_geom_m: Any,
    closure_line_m: Any,
    line_buffer_m: float,
) -> Tuple[float, Optional[float], Optional[float]]:
    """Return projected overlap span, centre projection, and angle difference.

    This is deliberately projection-based rather than distance-only. A side road
    that only touches/crosses a closure line usually has almost no projected span
    along the closure line, even though its distance to the line is 0 m.
    """
    if edge_geom_m is None or edge_geom_m.is_empty or closure_line_m is None or closure_line_m.is_empty:
        return 0.0, None, None
    if getattr(closure_line_m, "length", 0.0) <= 0:
        return 0.0, None, None

    tolerance = max(0.0, float(line_buffer_m))
    try:
        near_area = _flat_buffer(closure_line_m, tolerance)
        near_geom = edge_geom_m.intersection(near_area)
    except Exception:
        return 0.0, None, None

    best_span = 0.0
    best_center: Optional[float] = None
    best_angle_diff: Optional[float] = None
    closure_len = float(closure_line_m.length)

    for line_part in _iter_line_parts_only(near_geom):
        try:
            part_len = float(line_part.length)
        except Exception:
            continue
        if part_len <= 0.05:
            continue

        # Sample along the candidate's actual portion that lies near the closure.
        # The projected span along the closure line distinguishes a genuine
        # along-road overlap from a crossing/junction touch.
        samples = []
        sample_count = 7
        for i in range(sample_count):
            frac = i / (sample_count - 1)
            try:
                samples.append(line_part.interpolate(part_len * frac))
            except Exception:
                pass
        if not samples:
            continue

        try:
            projections = [float(closure_line_m.project(pt)) for pt in samples]
        except Exception:
            continue
        min_proj = max(0.0, min(projections))
        max_proj = min(closure_len, max(projections))
        span = max(0.0, max_proj - min_proj)
        center = (min_proj + max_proj) / 2.0

        edge_angle = _line_angle_degrees(line_part)
        closure_angle = _line_angle_at_projection(closure_line_m, center, max(5.0, min(30.0, max(span / 2.0, 5.0))))
        angle_diff = _angle_difference_180(edge_angle, closure_angle)

        if span > best_span:
            best_span = span
            best_center = center
            best_angle_diff = angle_diff

    return best_span, best_center, best_angle_diff


def _allow_named_line_candidate(
    edge_geom_m: Any,
    closure_line_m: Any,
    line_buffer_m: float,
) -> bool:
    """Named road matches can be accepted near endpoints, but not by a point touch.

    A continuing open road with the same name beyond the end of the closure line
    will normally project to a zero-length touch at the endpoint, so it is not
    blocked. The closed road segment itself still has positive projected overlap.
    """
    span, _, _ = _line_overlap_metrics(edge_geom_m, closure_line_m, line_buffer_m)
    return span >= 1.0


def _allow_distance_only_line_candidate(
    edge_geom_m: Any,
    closure_line_m: Any,
    line_buffer_m: float,
    endpoint_no_bleed_m: float,
    min_overlap_m: float,
    max_angle_deg: float,
) -> Tuple[bool, str]:
    """Strict line match for candidates without a road-name confirmation.

    This prevents the closure buffer from bleeding across intersections. A
    distance-only edge must overlap the body of the closure line for a meaningful
    projected length and have broadly the same bearing as the closure line.
    """
    span, center, angle_diff = _line_overlap_metrics(edge_geom_m, closure_line_m, line_buffer_m)
    if center is None:
        return False, "point/crossing touch only"

    closure_len = float(closure_line_m.length)
    min_overlap = max(0.0, float(min_overlap_m))
    if span < min_overlap:
        return False, "projected overlap too short/cross-road"

    # Exclude distance-only matches whose projected overlap is concentrated near
    # either closure endpoint. This is the zero-bleed-at-junction rule.
    endpoint_guard = max(0.0, float(endpoint_no_bleed_m))
    if closure_len > min_overlap:
        endpoint_guard = min(endpoint_guard, max(0.0, (closure_len - min_overlap) / 2.0))
    else:
        endpoint_guard = 0.0
    if endpoint_guard > 0 and (center <= endpoint_guard or center >= closure_len - endpoint_guard):
        return False, "inside endpoint no-bleed zone"

    if angle_diff is not None and angle_diff > max_angle_deg:
        return False, f"angle mismatch {angle_diff:.0f}deg"

    return True, "body overlap"


def match_one_geometry_to_edges(
    geom: Any,
    edge_index: EdgeIndex,
    *,
    point_block_radius_m: float,
    line_buffer_m: float,
    polygon_buffer_m: float,
    max_snap_distance_m: float,
    closure_road_name: str = "",
    line_endpoint_no_bleed_m: float = 30.0,
    line_distance_only_min_overlap_m: float = 8.0,
    line_distance_only_max_angle_deg: float = 35.0,
) -> Tuple[set[Tuple[Any, Any, Any]], Optional[float], str]:
    """Return blocked edge tuples, nearest edge distance, and notes."""
    blocked: set[Tuple[Any, Any, Any]] = set()
    nearest_d: Optional[float] = None
    notes: List[str] = []
    closure_road_names = road_name_variants(closure_road_name)

    if geom is None or geom.is_empty:
        return blocked, None, "empty geometry"

    for part in iter_geometries(geom):
        if part is None or part.is_empty:
            continue
        part_m = geom_to_m(part)
        part_type = part.geom_type

        if isinstance(part, Point):
            # Query broadly, then block edges within the smaller block radius. If
            # none are within block radius, block the single nearest edge if it is
            # within max_snap_distance_m. This avoids missing point closures that
            # are slightly offset from the centreline.
            query_area = part_m.buffer(max_snap_distance_m)
            candidates: List[Tuple[float, int]] = []
            seen = set()
            for idx in strtree_indices(edge_index, query_area):
                if idx in seen:
                    continue
                seen.add(idx)
                d = float(edge_index.edge_geoms_m[idx].distance(part_m))
                candidates.append((d, idx))
            candidates.sort(key=lambda x: x[0])
            if candidates:
                nearest_d = candidates[0][0] if nearest_d is None else min(nearest_d, candidates[0][0])
                close = [(d, idx) for d, idx in candidates if d <= point_block_radius_m]
                if close:
                    named_close = [(d, idx) for d, idx in close if road_names_match(edge_index.edge_names[idx], closure_road_names)]
                    named_candidates = [(d, idx) for d, idx in candidates if road_names_match(edge_index.edge_names[idx], closure_road_names)]
                    selected = named_close or (named_candidates[:1] if closure_road_names and named_candidates else close)
                    for _, idx in selected:
                        blocked.add(edge_index.edge_refs[idx].as_tuple())
                    name_note = " with matching road names" if named_close else ""
                    if closure_road_names and not named_close and named_candidates:
                        name_note = " using nearest matching road name"
                    notes.append(f"point: blocked {len(selected)} edge(s) within {point_block_radius_m:.0f}m{name_note}")
                elif candidates[0][0] <= max_snap_distance_m:
                    named_candidates = [(d, idx) for d, idx in candidates if road_names_match(edge_index.edge_names[idx], closure_road_names)]
                    selected = named_candidates[0] if named_candidates else candidates[0]
                    blocked.add(edge_index.edge_refs[selected[1]].as_tuple())
                    name_note = " with matching road name" if named_candidates else ""
                    notes.append(f"point: no edge inside block radius; blocked nearest edge at {selected[0]:.1f}m{name_note}")
            else:
                notes.append("point: no edge within max snap distance")

        elif isinstance(part, (LineString, MultiLineString)):
            # For line closures, the buffer is only a centreline-to-graph matching
            # tolerance. It is NOT allowed to spill across an intersection. A line
            # candidate must have positive projected overlap along the closure
            # body; distance-only candidates also need body overlap away from the
            # first/last endpoint and a broadly matching bearing.
            query_area = _flat_buffer(part_m, line_buffer_m)
            candidates: List[Tuple[float, int]] = []
            seen = set()
            for idx in strtree_indices(edge_index, query_area):
                if idx in seen:
                    continue
                seen.add(idx)
                edge_geom = edge_index.edge_geoms_m[idx]
                d = float(edge_geom.distance(part_m))
                nearest_d = d if nearest_d is None else min(nearest_d, d)
                if d <= line_buffer_m:
                    candidates.append((d, idx))

            selected: List[Tuple[float, int]] = []
            named_selected: List[Tuple[float, int]] = []
            distance_selected: List[Tuple[float, int]] = []
            rejected_endpoint = 0
            rejected_cross = 0
            rejected_angle = 0
            rejected_other = 0

            for d, idx in candidates:
                edge_geom = edge_index.edge_geoms_m[idx]
                name_match = road_names_match(edge_index.edge_names[idx], closure_road_names)
                if name_match and _allow_named_line_candidate(edge_geom, part_m, line_buffer_m):
                    selected.append((d, idx))
                    named_selected.append((d, idx))
                    continue

                ok, reason = _allow_distance_only_line_candidate(
                    edge_geom,
                    part_m,
                    line_buffer_m,
                    line_endpoint_no_bleed_m,
                    line_distance_only_min_overlap_m,
                    line_distance_only_max_angle_deg,
                )
                if ok:
                    selected.append((d, idx))
                    distance_selected.append((d, idx))
                else:
                    if "endpoint" in reason:
                        rejected_endpoint += 1
                    elif "cross" in reason or "short" in reason or "touch" in reason:
                        rejected_cross += 1
                    elif "angle" in reason:
                        rejected_angle += 1
                    else:
                        rejected_other += 1

            for _, idx in selected:
                blocked.add(edge_index.edge_refs[idx].as_tuple())

            note_bits = [
                f"line: blocked {len(selected)} of {len(candidates)} candidate edge(s) within {line_buffer_m:.0f}m",
                f"name-confirmed={len(named_selected)}",
                f"distance-body={len(distance_selected)}",
            ]
            rejects = []
            if rejected_endpoint:
                rejects.append(f"endpoint-no-bleed={rejected_endpoint}")
            if rejected_cross:
                rejects.append(f"cross/short-touch={rejected_cross}")
            if rejected_angle:
                rejects.append(f"angle-mismatch={rejected_angle}")
            if rejected_other:
                rejects.append(f"other-rejected={rejected_other}")
            if rejects:
                note_bits.append("rejected " + ", ".join(rejects))
            if closure_road_names and candidates and not named_selected:
                note_bits.append("no graph road-name match; used strict distance-only body matching")
            notes.append("; ".join(note_bits))

        elif isinstance(part, (Polygon, MultiPolygon)):
            # Polygons are uncommon but can represent an impacted area. Use the
            # polygon plus a small buffer.
            query_area = part_m.buffer(polygon_buffer_m)
            count = 0
            seen = set()
            for idx in strtree_indices(edge_index, query_area):
                if idx in seen:
                    continue
                seen.add(idx)
                d = float(edge_index.edge_geoms_m[idx].distance(part_m))
                nearest_d = d if nearest_d is None else min(nearest_d, d)
                if d <= polygon_buffer_m or edge_index.edge_geoms_m[idx].intersects(query_area):
                    blocked.add(edge_index.edge_refs[idx].as_tuple())
                    count += 1
            notes.append(f"polygon: blocked {count} edge(s)")

        else:
            # Fallback for unexpected geometries: use representative point.
            rep = part.representative_point()
            sub_blocked, sub_dist, sub_notes = match_one_geometry_to_edges(
                rep,
                edge_index,
                point_block_radius_m=point_block_radius_m,
                line_buffer_m=line_buffer_m,
                polygon_buffer_m=polygon_buffer_m,
                max_snap_distance_m=max_snap_distance_m,
                closure_road_name=closure_road_name,
                line_endpoint_no_bleed_m=line_endpoint_no_bleed_m,
                line_distance_only_min_overlap_m=line_distance_only_min_overlap_m,
                line_distance_only_max_angle_deg=line_distance_only_max_angle_deg,
            )
            blocked.update(sub_blocked)
            if sub_dist is not None:
                nearest_d = sub_dist if nearest_d is None else min(nearest_d, sub_dist)
            notes.append(f"fallback {part_type}: {sub_notes}")

    return blocked, nearest_d, "; ".join(notes)


def build_blocked_edges_for_scenario(
    closures: Sequence[Closure],
    edge_index: EdgeIndex,
    *,
    scenario_name: str,
    closure_filter: Callable[[Closure], bool],
    point_block_radius_m: float,
    line_buffer_m: float,
    polygon_buffer_m: float,
    max_snap_distance_m: float,
    line_endpoint_no_bleed_m: float,
    line_distance_only_min_overlap_m: float,
    line_distance_only_max_angle_deg: float,
) -> Tuple[set[Tuple[Any, Any, Any]], List[Dict[str, Any]], List[Dict[str, Any]], List[Closure]]:
    t0 = time.perf_counter()
    all_blocked: set[Tuple[Any, Any, Any]] = set()
    match_rows: List[Dict[str, Any]] = []
    unmatched_rows: List[Dict[str, Any]] = []
    matched_closures: List[Closure] = []

    considered = 0
    for c in closures:
        if not closure_filter(c):
            continue
        considered += 1
        blocked, nearest_d, notes = match_one_geometry_to_edges(
            c.geometry,
            edge_index,
            point_block_radius_m=point_block_radius_m,
            line_buffer_m=line_buffer_m,
            polygon_buffer_m=polygon_buffer_m,
            max_snap_distance_m=max_snap_distance_m,
            closure_road_name=c.road_name,
            line_endpoint_no_bleed_m=line_endpoint_no_bleed_m,
            line_distance_only_min_overlap_m=line_distance_only_min_overlap_m,
            line_distance_only_max_angle_deg=line_distance_only_max_angle_deg,
        )
        all_blocked.update(blocked)
        confidence = confidence_for_distance(nearest_d)
        base = closure_match_base_row(scenario_name, c)
        if blocked:
            matched_closures.append(c)
            row = {
                **base,
                "matched_edges": len(blocked),
                "nearest_edge_m": round(nearest_d, 1) if nearest_d is not None else "",
                "confidence": confidence,
                "match_status": "matched",
                "notes": notes,
            }
            match_rows.append(row)
        else:
            row = {
                **base,
                "matched_edges": 0,
                "nearest_edge_m": round(nearest_d, 1) if nearest_d is not None else "",
                "confidence": "unmatched",
                "match_status": "unmatched",
                "notes": notes,
            }
            match_rows.append(row)
            unmatched_rows.append(
                {
                    "scenario": scenario_name,
                    "closure_id": c.event_id,
                    "category_norm": c.category_norm,
                    "passability_norm": c.passability_norm,
                    "status_norm": c.status_norm,
                    "title": c.title,
                    "road_name": c.road_name,
                    "locality": c.locality,
                    "description": c.description,
                    "restrictions_text": c.restrictions_text,
                    "source_event_id": c.source_event_id,
                    "raw_advice": c.raw_advice,
                    "raw_event_type": c.raw_event_type,
                    "raw_event_subtype": c.raw_event_subtype,
                    "raw_impact_type": c.raw_impact_type,
                    "raw_impact_subtype": c.raw_impact_subtype,
                    "raw_properties_json": json.dumps(c.raw_properties or {}, ensure_ascii=False, default=str),
                    "geometry_type": c.geometry_type,
                    "nearest_edge_m": round(nearest_d, 1) if nearest_d is not None else "",
                    "reason": notes or "no matching road edge",
                    "url": c.url,
                }
            )

    print(
        f"[MATCH] scenario={scenario_name} considered={considered:,} matched={len(matched_closures):,} "
        f"blocked_edges={len(all_blocked):,} unmatched={len(unmatched_rows):,} elapsed={time.perf_counter() - t0:.1f}s"
    )
    return all_blocked, match_rows, unmatched_rows, matched_closures


# ---------------------------------------------------------------------
# Reachability
# ---------------------------------------------------------------------

def iter_adjacent_edges(G: nx.Graph, node: Any) -> Iterable[Tuple[Any, Tuple[Any, Any, Any]]]:
    """Yield neighbour and edge tuple. Handles directed/multigraph variants."""
    if G.is_multigraph():
        if G.is_directed():
            for u, v, k in G.out_edges(node, keys=True):
                yield v, (u, v, k)
            for u, v, k in G.in_edges(node, keys=True):
                yield u, (u, v, k)
        else:
            for u, v, k in G.edges(node, keys=True):
                other = v if u == node else u
                yield other, (u, v, k)
    else:
        if G.is_directed():
            for u, v in G.out_edges(node):
                yield v, (u, v, 0)
            for u, v in G.in_edges(node):
                yield u, (u, v, 0)
        else:
            for u, v in G.edges(node):
                other = v if u == node else u
                yield other, (u, v, 0)


def is_edge_blocked(edge: Tuple[Any, Any, Any], blocked_edges: set[Tuple[Any, Any, Any]]) -> bool:
    if edge in blocked_edges:
        return True
    # If graph has explicit reverse edge with a different key it should be
    # matched separately, but this helps if an undirected graph is used.
    return (edge[1], edge[0], edge[2]) in blocked_edges


def reachable_from_hubs(G: nx.Graph, hub_nodes: Sequence[Any], blocked_edges: set[Tuple[Any, Any, Any]]) -> set[Any]:
    queue = deque(n for n in hub_nodes if n is not None)
    seen: set[Any] = set()

    while queue:
        node = queue.popleft()
        if node in seen:
            continue
        seen.add(node)
        for neighbour, edge in iter_adjacent_edges(G, node):
            if is_edge_blocked(edge, blocked_edges):
                continue
            if neighbour not in seen:
                queue.append(neighbour)
    return seen


def hub_component_access(
    G: nx.Graph,
    hub_nodes: Sequence[Any],
    blocked_edges: set[Tuple[Any, Any, Any]],
) -> Tuple[Dict[Any, int], List[int]]:
    """Return each node's reachable hub count and all hub-containing component sizes."""
    hub_set = {n for n in hub_nodes if n is not None}
    node_hub_counts: Dict[Any, int] = {}
    hub_component_sizes: List[int] = []
    seen: set[Any] = set()

    for start in G.nodes:
        if start in seen:
            continue
        component_nodes: List[Any] = []
        component_hubs = 0
        queue = deque([start])
        seen.add(start)
        while queue:
            node = queue.popleft()
            component_nodes.append(node)
            if node in hub_set:
                component_hubs += 1
            for neighbour, edge in iter_adjacent_edges(G, node):
                if neighbour in seen or is_edge_blocked(edge, blocked_edges):
                    continue
                seen.add(neighbour)
                queue.append(neighbour)

        if component_hubs:
            hub_component_sizes.append(component_hubs)
            for node in component_nodes:
                node_hub_counts[node] = component_hubs

    return node_hub_counts, sorted(hub_component_sizes, reverse=True)


def graph_component_node_sizes(
    G: nx.Graph,
    blocked_edges: set[Tuple[Any, Any, Any]],
) -> Dict[Any, int]:
    """Return the graph component size for each node under a blocking scenario."""
    node_component_sizes: Dict[Any, int] = {}
    seen: set[Any] = set()

    for start in G.nodes:
        if start in seen:
            continue
        component_nodes: List[Any] = []
        queue = deque([start])
        seen.add(start)
        while queue:
            node = queue.popleft()
            component_nodes.append(node)
            for neighbour, edge in iter_adjacent_edges(G, node):
                if neighbour in seen or is_edge_blocked(edge, blocked_edges):
                    continue
                seen.add(neighbour)
                queue.append(neighbour)

        size = len(component_nodes)
        for node in component_nodes:
            node_component_sizes[node] = size

    return node_component_sizes


QLD_STATE_BORDER_SEGMENTS: List[Tuple[str, Tuple[float, float], Tuple[float, float]]] = [
    ("NT", (138.0, -26.0), (138.0, -16.0)),
    ("SA", (138.0, -29.0), (141.0, -29.0)),
    # Approximate the southern Queensland border for this reachability diagnostic.
    # This is deliberately used only to label graph components that have practical
    # access to a state border, not for legal boundary mapping.
    ("NSW", (141.0, -29.0), (153.65, -28.15)),
]


def state_border_node_labels(G: nx.Graph, max_distance_m: float) -> Dict[Any, List[str]]:
    """Return graph nodes that are close enough to the SA/NT/NSW borders."""
    border_lines = []
    for name, a, b in QLD_STATE_BORDER_SEGMENTS:
        ax, ay = point_wgs_to_m(a[0], a[1])
        bx, by = point_wgs_to_m(b[0], b[1])
        border_lines.append((name, LineString([(ax, ay), (bx, by)])))

    out: Dict[Any, List[str]] = {}
    for node, data in G.nodes(data=True):
        try:
            lon = float(data["x"])
            lat = float(data["y"])
        except Exception:
            continue
        x, y = point_wgs_to_m(lon, lat)
        p = Point(x, y)
        labels = [name for name, line in border_lines if line.distance(p) <= max_distance_m]
        if labels:
            out[node] = sorted(set(labels))
    return out


def border_component_access(
    G: nx.Graph,
    border_node_labels: Dict[Any, List[str]],
    blocked_edges: set[Tuple[Any, Any, Any]],
) -> Tuple[Dict[Any, int], Dict[Any, str]]:
    """Return each node's reachable border count/names under a blocking scenario."""
    node_border_counts: Dict[Any, int] = {}
    node_border_names: Dict[Any, str] = {}
    seen: set[Any] = set()

    for start in G.nodes:
        if start in seen:
            continue
        component_nodes: List[Any] = []
        component_borders: set[str] = set()
        queue = deque([start])
        seen.add(start)
        while queue:
            node = queue.popleft()
            component_nodes.append(node)
            component_borders.update(border_node_labels.get(node, []))
            for neighbour, edge in iter_adjacent_edges(G, node):
                if neighbour in seen or is_edge_blocked(edge, blocked_edges):
                    continue
                seen.add(neighbour)
                queue.append(neighbour)

        if component_borders:
            border_names = ", ".join(sorted(component_borders))
            border_count = len(component_borders)
            for node in component_nodes:
                node_border_counts[node] = border_count
                node_border_names[node] = border_names

    return node_border_counts, node_border_names


def summarise_hub_components(component_sizes: Sequence[int]) -> Dict[str, Any]:
    return {
        "components_with_hubs": len(component_sizes),
        "largest_hub_component_size": max(component_sizes) if component_sizes else 0,
        "single_hub_components": sum(1 for size in component_sizes if size == 1),
    }


def snap_places_to_graph(
    places: Sequence[Place],
    node_index: NodeIndex,
    *,
    max_snap_distance_m: float,
) -> Tuple[Dict[str, Any], Dict[str, Optional[float]]]:
    place_node: Dict[str, Any] = {}
    place_dist: Dict[str, Optional[float]] = {}
    dropped = 0
    for p in places:
        node, dist = nearest_node(node_index, p.lat, p.lon, max_snap_distance_m)
        place_node[p.place_id] = node
        place_dist[p.place_id] = dist
        if node is None:
            dropped += 1
    if dropped:
        print(f"[SNAP] places/hubs beyond {max_snap_distance_m:.0f}m from graph: {dropped}/{len(places)}")
    return place_node, place_dist


def smart_resnap_to_hub_connected_nodes(
    places: Sequence[Place],
    node_index: NodeIndex,
    place_nodes: Dict[str, Any],
    place_dist: Dict[str, Optional[float]],
    hub_counts_before: Dict[Any, int],
    component_node_sizes_before: Dict[Any, int],
    *,
    enabled: bool,
    max_component_nodes: int,
    max_distance_m: float,
    k_nearest: int,
) -> Tuple[Dict[str, str], Dict[str, str]]:
    """Conservatively move tiny disconnected-component snaps to nearby hub-connected nodes.

    The initial nearest-node snap is retained unless a place is snapped to a
    small pre-closure component and a hub-connected node is nearby. This avoids
    masking genuinely disconnected large graph components while repairing common
    tiny-component snap artefacts.
    """
    snap_strategy: Dict[str, str] = {}
    snap_note: Dict[str, str] = {}

    for p in places:
        node = place_nodes.get(p.place_id)
        dist = place_dist.get(p.place_id)

        if node is None:
            snap_strategy[p.place_id] = "not_snapped"
            if dist is None:
                snap_note[p.place_id] = "No graph node found within the configured snap distance."
            else:
                snap_note[p.place_id] = f"Nearest graph node is {float(dist):.1f} m away, beyond the configured snap distance."
            continue

        snap_strategy[p.place_id] = "nearest"
        if node in hub_counts_before:
            snap_note[p.place_id] = "Nearest graph node is already in a pre-closure hub-connected component."
            continue

        component_size = component_node_sizes_before.get(node, 0)
        if not enabled:
            snap_note[p.place_id] = "Nearest graph node is not hub-connected; smart re-snap disabled."
            continue
        if component_size > max_component_nodes:
            snap_note[p.place_id] = (
                f"Nearest graph node is in a disconnected component of {component_size} nodes, "
                f"larger than the smart re-snap limit of {max_component_nodes}."
            )
            continue

        best_node: Optional[Any] = None
        best_dist: Optional[float] = None
        for candidate, candidate_dist in nearby_nodes(
            node_index,
            p.lat,
            p.lon,
            max_dist_m=max_distance_m,
            k_nearest=k_nearest,
        ):
            if candidate in hub_counts_before:
                best_node = candidate
                best_dist = candidate_dist
                break

        if best_node is None or best_dist is None:
            snap_note[p.place_id] = (
                f"Nearest graph node is in a disconnected component of {component_size} nodes; "
                f"no hub-connected node found within {max_distance_m:.0f} m."
            )
            continue

        old_node = node
        old_dist = dist
        place_nodes[p.place_id] = best_node
        place_dist[p.place_id] = best_dist
        snap_strategy[p.place_id] = "smart_hub_connected"
        snap_note[p.place_id] = (
            f"Nearest graph node {old_node} was in a tiny disconnected component of {component_size} nodes"
            f"{f' at {float(old_dist):.1f} m' if old_dist is not None else ''}; "
            f"re-snapped to nearby pre-closure hub-connected node {best_node} at {best_dist:.1f} m."
        )

    return snap_strategy, snap_note


def nearest_closures_for_place(
    place: Place,
    closures: Sequence[Closure],
    limit: int = 5,
) -> List[Dict[str, Any]]:
    if not closures:
        return []
    px, py = point_wgs_to_m(place.lon, place.lat)
    p_m = Point(px, py)
    ranked: List[Tuple[float, Closure]] = []
    for c in closures:
        if c.geometry is None or c.geometry.is_empty:
            continue
        try:
            d = float(geom_to_m(c.geometry).distance(p_m))
        except Exception:
            continue
        ranked.append((d, c))
    ranked.sort(key=lambda x: x[0])
    out: List[Dict[str, Any]] = []
    for d, c in ranked[:limit]:
        out.append(
            {
                "closure_id": c.event_id,
                "source_event_id": c.source_event_id,
                "distance_m": round(d, 1),
                "category_norm": c.category_norm,
                "passability_norm": c.passability_norm,
                "status_norm": c.status_norm,
                "reason_norm": c.reason_norm,
                "title": c.title,
                "description": c.description,
                "road_name": c.road_name,
                "locality": c.locality,
                "restrictions_text": c.restrictions_text,
                "raw_advice": c.raw_advice,
                "raw_event_type": c.raw_event_type,
                "raw_event_subtype": c.raw_event_subtype,
                "raw_impact_type": c.raw_impact_type,
                "raw_impact_subtype": c.raw_impact_subtype,
                "url": c.url,
            }
        )
    return out


def classify_places(
    places: Sequence[Place],
    place_nodes: Dict[str, Any],
    place_dist: Dict[str, Optional[float]],
    snap_strategy: Dict[str, str],
    snap_note: Dict[str, str],
    reachable_before: set[Any],
    reachable_impassable: set[Any],
    reachable_all: set[Any],
    hub_counts_before: Dict[Any, int],
    hub_counts_impassable: Dict[Any, int],
    hub_counts_all: Dict[Any, int],
    border_counts_before: Dict[Any, int],
    border_names_before: Dict[Any, str],
    matched_impassable_closures: Sequence[Closure],
    matched_all_blocking_closures: Sequence[Closure],
    hub_routes: Optional[Dict[str, Dict[str, Any]]] = None,
) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    for p in places:
        node = place_nodes.get(p.place_id)
        snap_dist = place_dist.get(p.place_id)

        before = bool(node in reachable_before) if node is not None else False
        imp = bool(node in reachable_impassable) if node is not None else False
        allb = bool(node in reachable_all) if node is not None else False
        before_hubs = hub_counts_before.get(node, 0) if node is not None else 0
        imp_hubs = hub_counts_impassable.get(node, 0) if node is not None else 0
        all_hubs = hub_counts_all.get(node, 0) if node is not None else 0
        before_borders = border_counts_before.get(node, 0) if node is not None else 0
        before_border_names = border_names_before.get(node, "") if node is not None else ""
        hub_warning = ""
        if allb and all_hubs == 1:
            hub_warning = "Place can reach only one hub when restricted/conditional closures are also blocked; that hub cannot reach another modelled hub under this scenario."
        elif imp and imp_hubs == 1:
            hub_warning = "Place can reach only one hub when full closures are blocked; that hub cannot reach another modelled hub under this scenario."

        if node is None:
            category = "unknown_place_not_snapped"
            confidence = "unknown"
            reason = "Place could not be snapped to the road graph within the configured distance."
            nearest = []
        elif not before:
            if before_borders:
                category = "isolated_from_qld_hubs_border_access"
                confidence = "unknown"
                reason = (
                    "Place could not reach a modelled Queensland hub even before current closures were applied, "
                    f"but can reach the {before_border_names} state border."
                )
            else:
                category = "unknown_preexisting_disconnected"
                confidence = "unknown"
                reason = "Place could not reach a hub even before current closures were applied; this is likely a graph/data issue or a genuinely disconnected place."
            nearest = []
        elif not imp:
            category = "isolated_full_closures"
            confidence = "medium"
            reason = "Place could reach a hub before closures, but cannot reach any hub after active impassable closures are blocked."
            nearest = nearest_closures_for_place(p, matched_impassable_closures)
            if nearest and nearest[0].get("distance_m", 999999) <= 5000:
                confidence = "high"
        elif not allb:
            category = "isolated_with_restrictions"
            confidence = "medium"
            reason = "Place can still reach a hub with only impassable closures blocked, but not when restricted/conditional-access closures are also blocked."
            nearest = nearest_closures_for_place(p, matched_all_blocking_closures)
            if nearest and nearest[0].get("distance_m", 999999) <= 5000:
                confidence = "medium"
        else:
            category = "not_isolated"
            confidence = "high"
            reason = "Place still has hub access under both closure scenarios."
            nearest = []

        route = (hub_routes or {}).get(p.place_id, {})

        rows.append(
            {
                "place_id": p.place_id,
                "name": p.name,
                "place_type": p.place_type,
                "state": p.state,
                "lga": p.lga,
                "lat": p.lat,
                "lon": p.lon,
                "is_hub": p.is_hub,
                "nearest_node": node if node is not None else "",
                "snap_distance_m": round(float(snap_dist), 1) if snap_dist is not None else "",
                "snap_strategy": snap_strategy.get(p.place_id) or ("not_snapped" if node is None else "nearest"),
                "snap_note": snap_note.get(p.place_id, ""),
                "hub_access_before": before,
                "hub_access_impassable_only": imp,
                "hub_access_all_blocking": allb,
                "reachable_hubs_before": before_hubs,
                "reachable_hubs_impassable_only": imp_hubs,
                "reachable_hubs_all_blocking": all_hubs,
                "state_border_access_before": bool(before_borders),
                "reachable_state_borders_before": before_border_names,
                "hub_network_warning": hub_warning,
                "isolation_category": category,
                "isolation_confidence": confidence,
                "isolation_reason": reason,
                "nearby_blocking_closures_json": json.dumps(nearest, ensure_ascii=False),
                "hub_route_name": route.get("hub_name", ""),
                "hub_route_distance_m": round(float(route.get("distance_m", 0)), 1) if route else "",
                "hub_route_geojson": json.dumps(route.get("geometry"), ensure_ascii=False) if route else "",
            }
        )
    return rows


# ---------------------------------------------------------------------
# Writers
# ---------------------------------------------------------------------

def write_csv(path: Path, rows: Iterable[Dict[str, Any]], fields: Sequence[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(fields), extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def write_geojson(path: Path, features: List[Dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {"type": "FeatureCollection", "features": features}
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")


def place_rows_to_geojson(rows: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    features: List[Dict[str, Any]] = []
    for r in rows:
        try:
            lat = float(r["lat"])
            lon = float(r["lon"])
        except Exception:
            continue
        props = dict(r)
        props.pop("lat", None)
        props.pop("lon", None)
        features.append({"type": "Feature", "geometry": {"type": "Point", "coordinates": [lon, lat]}, "properties": props})
    return features


def write_outputs(
    out_dir: Path,
    closures: Sequence[Closure],
    source_meta: Dict[str, Any],
    place_rows: Sequence[Dict[str, Any]],
    match_rows: Sequence[Dict[str, Any]],
    unmatched_rows: Sequence[Dict[str, Any]],
    summary: Dict[str, Any],
) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)

    write_csv(out_dir / "closures_qld_current.csv", [c.to_csv_row() for c in closures], CLOSURE_CSV_FIELDS)
    write_geojson(out_dir / "closures_qld_current.geojson", [c.to_feature() for c in closures])
    (out_dir / "sources_run_qld.json").write_text(json.dumps(source_meta, ensure_ascii=False, indent=2), encoding="utf-8")

    write_csv(out_dir / "qld_place_isolation_current.csv", place_rows, PLACE_CSV_FIELDS)
    isolated_rows = [r for r in place_rows if r.get("isolation_category") in {"isolated_full_closures", "isolated_with_restrictions"}]
    write_csv(out_dir / "isolated_places_qld.csv", isolated_rows, PLACE_CSV_FIELDS)

    write_geojson(out_dir / "qld_place_isolation_current.geojson", place_rows_to_geojson(place_rows))
    write_geojson(out_dir / "isolated_places_qld.geojson", place_rows_to_geojson(isolated_rows))

    write_csv(out_dir / "closure_match_report_qld.csv", match_rows, MATCH_CSV_FIELDS)
    write_csv(out_dir / "unmatched_closures_qld.csv", unmatched_rows, UNMATCHED_CSV_FIELDS)

    (out_dir / "qld_isolation_summary.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8")


# ---------------------------------------------------------------------
# Main analysis runner
# ---------------------------------------------------------------------

def run_analysis(args: argparse.Namespace) -> Dict[str, Any]:
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    # Load closures.
    if args.closures_geojson:
        closures, source_meta = load_closures_from_geojson(Path(args.closures_geojson), include_planned=args.include_planned)
    elif args.closures_csv:
        closures, source_meta = load_closures_from_csv(Path(args.closures_csv), include_planned=args.include_planned)
    else:
        print("[FETCH] QLD Traffic current events")
        closures, source_meta = fetch_qld_closures(include_planned=args.include_planned, timeout_s=args.http_timeout_s)

    print(f"[CLOSURES] normalised={len(closures):,}")
    active_closures = [c for c in closures if is_active_closure(c)]
    imp_closures = [c for c in closures if is_impassable_blocking(c)]
    all_blocking_closures = [c for c in closures if is_all_blocking(c)]
    print(f"[CLOSURES] active={len(active_closures):,} impassable_blocking={len(imp_closures):,} all_blocking={len(all_blocking_closures):,}")

    # Load places and hubs.
    places = load_places(Path(args.places), qld_only=not args.no_qld_bbox_filter)
    hubs = [p for p in places if p.is_hub]
    if not places:
        raise RuntimeError("No places loaded. Check --places and lat/lon column names.")
    if not hubs:
        raise RuntimeError("No hubs found. Add is_hub=1 rows to places.csv for major/regional anchor places.")
    print(f"[PLACES] places={len(places):,} hubs={len(hubs):,}")

    # Load graph and indexes.
    G = load_graph(Path(args.graph))
    if getattr(args, "manual_connectors", ""):
        apply_manual_connectors(G, Path(args.manual_connectors))
    node_index = build_node_index(G)
    edge_index = build_edge_index(G)

    # Snap places and hubs. Hubs use the same max distance so bad hub coords are
    # visible rather than silently snapped hundreds of kilometres away.
    place_nodes, place_dist = snap_places_to_graph(places, node_index, max_snap_distance_m=args.max_place_snap_m)
    hub_nodes_by_place_id = {h.place_id: place_nodes.get(h.place_id) for h in hubs if place_nodes.get(h.place_id) is not None}
    hub_nodes = list(hub_nodes_by_place_id.values())
    if not hub_nodes:
        raise RuntimeError("No hubs snapped to the graph. Increase --max-place-snap-m or check hub coordinates.")
    print(f"[SNAP] snapped_hubs={len(hub_nodes):,}/{len(hubs):,}")

    # Match closures to edges in both scenarios.
    blocked_imp, match_imp, unmatched_imp, matched_imp_closures = build_blocked_edges_for_scenario(
        closures,
        edge_index,
        scenario_name="impassable_only",
        closure_filter=is_impassable_blocking,
        point_block_radius_m=args.point_block_radius_m,
        line_buffer_m=args.line_buffer_m,
        polygon_buffer_m=args.polygon_buffer_m,
        max_snap_distance_m=args.max_closure_snap_m,
        line_endpoint_no_bleed_m=args.line_endpoint_no_bleed_m,
        line_distance_only_min_overlap_m=args.line_distance_only_min_overlap_m,
        line_distance_only_max_angle_deg=args.line_distance_only_max_angle_deg,
    )
    blocked_all, match_all, unmatched_all, matched_all_closures = build_blocked_edges_for_scenario(
        closures,
        edge_index,
        scenario_name="all_blocking",
        closure_filter=is_all_blocking,
        point_block_radius_m=args.point_block_radius_m,
        line_buffer_m=args.line_buffer_m,
        polygon_buffer_m=args.polygon_buffer_m,
        max_snap_distance_m=args.max_closure_snap_m,
        line_endpoint_no_bleed_m=args.line_endpoint_no_bleed_m,
        line_distance_only_min_overlap_m=args.line_distance_only_min_overlap_m,
        line_distance_only_max_angle_deg=args.line_distance_only_max_angle_deg,
    )

    # Reachability before and after closures.
    t0 = time.perf_counter()
    hub_counts_before, hub_components_before = hub_component_access(G, hub_nodes, blocked_edges=set())
    reachable_before = set(hub_counts_before)
    print(f"[REACH] before closures reachable_nodes={len(reachable_before):,} hub_components={len(hub_components_before):,} elapsed={time.perf_counter() - t0:.1f}s")
    component_node_sizes_before = graph_component_node_sizes(G, blocked_edges=set())
    border_node_labels = state_border_node_labels(G, max_distance_m=args.state_border_access_distance_m)
    border_counts_before, border_names_before = border_component_access(G, border_node_labels, blocked_edges=set())
    print(f"[REACH] state_border_access border_nodes={len(border_node_labels):,} reachable_nodes={len(border_counts_before):,}")

    t0 = time.perf_counter()
    hub_counts_imp, hub_components_imp = hub_component_access(G, hub_nodes, blocked_edges=blocked_imp)
    reachable_imp = set(hub_counts_imp)
    print(f"[REACH] impassable_only reachable_nodes={len(reachable_imp):,} hub_components={len(hub_components_imp):,} elapsed={time.perf_counter() - t0:.1f}s")

    t0 = time.perf_counter()
    hub_counts_all, hub_components_all = hub_component_access(G, hub_nodes, blocked_edges=blocked_all)
    reachable_all = set(hub_counts_all)
    print(f"[REACH] all_blocking reachable_nodes={len(reachable_all):,} hub_components={len(hub_components_all):,} elapsed={time.perf_counter() - t0:.1f}s")

    snap_strategy, snap_note = smart_resnap_to_hub_connected_nodes(
        places,
        node_index,
        place_nodes,
        place_dist,
        hub_counts_before,
        component_node_sizes_before,
        enabled=not args.no_smart_resnap,
        max_component_nodes=args.smart_resnap_max_component_nodes,
        max_distance_m=args.smart_resnap_max_distance_m,
        k_nearest=args.smart_resnap_k_nearest,
    )
    smart_count = sum(1 for strategy in snap_strategy.values() if strategy == "smart_hub_connected")
    if smart_count:
        print(f"[SNAP] smart re-snapped tiny disconnected place components to nearby hub-connected nodes: {smart_count:,}")

    place_rows = classify_places(
        places,
        place_nodes,
        place_dist,
        snap_strategy,
        snap_note,
        reachable_before,
        reachable_imp,
        reachable_all,
        hub_counts_before,
        hub_counts_imp,
        hub_counts_all,
        border_counts_before,
        border_names_before,
        matched_imp_closures,
        matched_all_closures,
    )

    t0 = time.perf_counter()
    hub_routes = build_hub_access_routes(G, places, place_nodes, hub_nodes_by_place_id, place_rows, blocked_all)
    print(f"[ROUTES] current open hub routes generated for not-isolated places: {len(hub_routes):,} elapsed={time.perf_counter() - t0:.1f}s")
    if hub_routes:
        place_rows = classify_places(
            places,
            place_nodes,
            place_dist,
            snap_strategy,
            snap_note,
            reachable_before,
            reachable_imp,
            reachable_all,
            hub_counts_before,
            hub_counts_imp,
            hub_counts_all,
            border_counts_before,
            border_names_before,
            matched_imp_closures,
            matched_all_closures,
            hub_routes,
        )

    counts_by_category: Dict[str, int] = {}
    for r in place_rows:
        key = str(r.get("isolation_category"))
        counts_by_category[key] = counts_by_category.get(key, 0) + 1

    match_rows = match_imp + match_all
    unmatched_rows = unmatched_imp + unmatched_all

    summary = {
        "created_at": utc_now_iso(),
        "script": Path(__file__).name,
        "inputs": {
            "graph": str(args.graph),
            "places": str(args.places),
            "closures_geojson": str(args.closures_geojson or ""),
            "closures_csv": str(args.closures_csv or ""),
            "include_planned": bool(args.include_planned),
        },
        "parameters": {
            "point_block_radius_m": args.point_block_radius_m,
            "line_buffer_m": args.line_buffer_m,
            "polygon_buffer_m": args.polygon_buffer_m,
            "max_closure_snap_m": args.max_closure_snap_m,
            "max_place_snap_m": args.max_place_snap_m,
            "smart_resnap_enabled": not args.no_smart_resnap,
            "smart_resnap_max_component_nodes": args.smart_resnap_max_component_nodes,
            "smart_resnap_max_distance_m": args.smart_resnap_max_distance_m,
            "smart_resnap_k_nearest": args.smart_resnap_k_nearest,
            "state_border_access_distance_m": args.state_border_access_distance_m,
        },
        "closure_source": source_meta,
        "counts": {
            "closures_normalised": len(closures),
            "closures_active": len(active_closures),
            "closures_impassable_blocking": len(imp_closures),
            "closures_all_blocking": len(all_blocking_closures),
            "places": len(places),
            "hubs": len(hubs),
            "snapped_hubs": len(hub_nodes),
            "graph_nodes": G.number_of_nodes(),
            "graph_edges": G.number_of_edges(),
            "blocked_edges_impassable_only": len(blocked_imp),
            "blocked_edges_all_blocking": len(blocked_all),
            "reachable_nodes_before": len(reachable_before),
            "state_border_nodes": len(border_node_labels),
            "state_border_reachable_nodes_before": len(border_counts_before),
            "reachable_nodes_impassable_only": len(reachable_imp),
            "reachable_nodes_all_blocking": len(reachable_all),
            "hub_components_before": summarise_hub_components(hub_components_before),
            "hub_components_impassable_only": summarise_hub_components(hub_components_imp),
            "hub_components_all_blocking": summarise_hub_components(hub_components_all),
            "smart_resnapped_places": smart_count,
            "not_isolated_hub_routes": len(hub_routes),
            "place_categories": counts_by_category,
            "unmatched_closure_rows": len(unmatched_rows),
        },
        "outputs": {
            "closures_csv": str(out_dir / "closures_qld_current.csv"),
            "closures_geojson": str(out_dir / "closures_qld_current.geojson"),
            "places_csv": str(out_dir / "qld_place_isolation_current.csv"),
            "isolated_csv": str(out_dir / "isolated_places_qld.csv"),
            "places_geojson": str(out_dir / "qld_place_isolation_current.geojson"),
            "isolated_geojson": str(out_dir / "isolated_places_qld.geojson"),
            "match_report_csv": str(out_dir / "closure_match_report_qld.csv"),
            "unmatched_closures_csv": str(out_dir / "unmatched_closures_qld.csv"),
            "summary_json": str(out_dir / "qld_isolation_summary.json"),
        },
        "notes": [
            "isolated_full_closures means the place had hub access before closures but not after impassable closures were blocked.",
            "isolated_with_restrictions means the place still has access under full-closure blocking, but loses access when restricted/conditional-access events are also blocked.",
            "hub_network_warning is set when a place can reach only one modelled hub in the relevant closure scenario, meaning that hub cannot reach another modelled hub even though the place still has local hub access.",
            "unknown_preexisting_disconnected means the place could not reach a hub even before applying current closures, so it is not safe to attribute isolation to current closures.",
            "This is an automated graph estimate, not an authoritative emergency-services isolation declaration.",
        ],
    }

    write_outputs(out_dir, closures, source_meta, place_rows, match_rows, unmatched_rows, summary)
    print(f"[OUT] wrote outputs to: {out_dir}")
    print("[SUMMARY] place categories:")
    for k, v in sorted(counts_by_category.items()):
        print(f"  - {k}: {v}")
    return summary


# ---------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run Queensland road closure isolation analysis against a road graph and places list.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--graph", default="network_cache/qld_drive.graphml", help="Queensland road graph GraphML path.")
    parser.add_argument("--places", default="places.csv", help="Places CSV with name/lat/lon and is_hub=1 rows.")
    parser.add_argument("--out-dir", default="out_isolation", help="Output directory.")
    parser.add_argument("--closures-geojson", default="", help="Use an existing closure GeoJSON instead of fetching live QLD Traffic.")
    parser.add_argument("--closures-csv", default="", help="Use an existing normalised closure CSV instead of fetching live QLD Traffic.")
    parser.add_argument("--include-planned", action="store_true", help="Include planned/roadworks events.")
    parser.add_argument("--no-qld-bbox-filter", action="store_true", help="Do not filter places to the Queensland bbox.")
    parser.add_argument("--http-timeout-s", type=float, default=30.0, help="HTTP timeout for live QLD Traffic fetch.")

    parser.add_argument("--point-block-radius-m", type=float, default=75.0, help="Block all road edges within this radius of point closures.")
    parser.add_argument("--line-buffer-m", type=float, default=10.0, help="Tolerance for matching line-closure centrelines to graph edges. The buffer is not allowed to bleed across intersections.")
    parser.add_argument("--line-endpoint-no-bleed-m", type=float, default=30.0, help="For distance-only line matches, reject graph edges whose overlap is concentrated within this distance of a closure line endpoint.")
    parser.add_argument("--line-distance-only-min-overlap-m", type=float, default=8.0, help="Minimum projected overlap along the closure line required before a no-road-name line candidate can be blocked.")
    parser.add_argument("--line-distance-only-max-angle-deg", type=float, default=35.0, help="Maximum bearing difference allowed for no-road-name line candidates.")
    parser.add_argument("--polygon-buffer-m", type=float, default=25.0, help="Additional buffer around polygon closures/impact areas.")
    parser.add_argument("--max-closure-snap-m", type=float, default=300.0, help="Maximum distance allowed when snapping a closure to the road graph.")
    parser.add_argument("--max-place-snap-m", type=float, default=5000.0, help="Maximum distance allowed when snapping places/hubs to the road graph.")
    parser.add_argument("--no-smart-resnap", action="store_true", help="Disable conservative re-snapping from tiny disconnected components to nearby pre-closure hub-connected nodes.")
    parser.add_argument("--smart-resnap-max-component-nodes", type=int, default=10, help="Maximum disconnected component size eligible for smart re-snapping.")
    parser.add_argument("--smart-resnap-max-distance-m", type=float, default=2000.0, help="Maximum distance to a hub-connected node for smart re-snapping.")
    parser.add_argument("--smart-resnap-k-nearest", type=int, default=250, help="Number of nearby graph nodes to inspect during smart re-snapping.")
    parser.add_argument("--state-border-access-distance-m", type=float, default=5000.0, help="Distance from the SA/NT/NSW border used to label non-hub-connected components with state-border access.")
    parser.add_argument("--manual-connectors", default="", help="Optional CSV of audited manual graph connector edges to apply before analysis.")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        run_analysis(args)
        return 0
    except KeyboardInterrupt:
        print("Interrupted.", file=sys.stderr)
        return 130
    except Exception as exc:
        print(f"[ERROR] {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
