# -*- coding: utf-8 -*-
"""Rule-based Houdini network preflight for RBD, APEX, KineFX and SOP networks.

This module is intentionally a single file so it can be launched from a shelf::

    from __future__ import annotations
    import runpy
    tool = runpy.run_path(r"C:\\path\\houdini_network_preflight.py")
    tool["show_preflight_ui"]()

The analyzer is read-only.  It does not repair nodes or save the scene.  Standard
and Deep scans may cook SOP geometry; the UI makes that cost explicit.
"""

from __future__ import annotations

import datetime as _datetime
import hashlib
import json
import math
import os
import re
import traceback
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Set, Tuple

try:
    import hou  # type: ignore
except ImportError:
    hou = None  # type: ignore

try:
    import apex  # type: ignore
except ImportError:
    apex = None  # type: ignore


TOOL_NAME = "Houdini Network Preflight"
VERSION = "0.3.5"
SCHEMA = "houdini-network-preflight-v3"

SEVERITY_SCORE = {
    "critical": 400,
    "error": 300,
    "warning": 200,
    "notice": 100,
    "info": 0,
}
CONFIDENCE_SCORE = {"high": 30, "medium": 20, "low": 10}
SEVERITY_LABEL_JA = {
    "critical": "重大",
    "error": "エラー",
    "warning": "警告",
    "notice": "注意",
    "info": "情報",
}

RBD_TYPE_HINTS = (
    "rbd",
    "bullet",
    "fracture",
    "constraint",
    "voronoi",
    "cluster",
)
APEX_TYPE_HINTS = ("apex::", "apex.", "sceneanimate", "packfolder", "unpackfolder")
KINEFX_TYPE_HINTS = (
    "kinefx::",
    "skeleton",
    "joint",
    "rigpose",
    "characterpack",
    "characterunpack",
    "motionclip",
    "retarget",
)
CACHE_TYPE_HINTS = ("filecache", "cache", "rop_geometry", "geometryrop")
ATTRIBUTE_NODE_HINTS = (
    "attribcreate",
    "attribdelete",
    "attribpromote",
    "attribcopy",
    "attribrandomize",
    "attribute",
    "name",
    "connectivity",
    "group",
)

WATCH_ATTRIBUTES = (
    "name",
    "path",
    "source_piece_name",
    "parent_name",
    "root_name",
    "sourceprim",
    "piece",
    "class",
    "cluster",
    "active",
    "animated",
    "deforming",
    "v",
    "w",
    "orient",
    "scale",
    "pscale",
    "mass",
    "density",
    "friction",
    "bounce",
    "bullet_collision_margin",
    "bullet_shrink_amount",
    "bullet_georep",
    "constraint_name",
    "constraint_type",
    "strength",
    "restlength",
    "rest_length",
    "impulse_halflife",
    "propagate_rate",
    "propagationiterations",
    "transform",
    "localtransform",
    "rest_transform",
    "parent",
    "boneCapture",
    "clipinfo",
    "time",
)
PROTECTED_ATTRIBUTES = {
    "name",
    "sourceprim",
    "active",
    "animated",
    "constraint_name",
    "strength",
    "transform",
    "boneCapture",
}

IDENTITY_ATTRIBUTES = {
    "name",
    "path",
    "source_piece_name",
    "parent_name",
    "root_name",
}

# Only these rule results are represented as FAIL in the LLM packet.  Other
# findings remain REVIEW even when their UI priority is high.  This prevents a
# small receiving model from treating every heuristic as an established fault.
LLM_FAIL_RULES = {
    "NODE_REQUIRED_INPUT_MISSING",
    "FILE_INPUT_MISSING",
    "GEOMETRY_INVALID",
    "ATTRIBUTE_NONFINITE_VALUES",
    "PACKED_TRANSFORM_SINGULAR",
    "RBD_GEOMETRY_NAME_MISSING",
    "RBD_GEOMETRY_EMPTY_NAMES",
    "RBD_GEOMETRY_DUPLICATE_NAMES",
    "RBD_PROXY_EMPTY",
    "RBD_PROXY_NAME_MISSING",
    "RBD_PROXY_DUPLICATE_NAMES",
    "RBD_GEOMETRY_PROXY_NAME_MISMATCH",
    "RBD_CONSTRAINT_ENDPOINT_NAME_MISSING",
    "RBD_CONSTRAINT_ORPHAN_ENDPOINTS",
    "RBD_CONSTRAINT_NAME_MISSING",
    "RBD_GLUE_STRENGTH_MISSING",
    "RBD_ALL_GLUE_ZERO_STRENGTH",
    "APEX_GRAPH_LOAD_EXCEPTION",
    "APEX_GRAPH_ENUMERATION_FAILED",
    "APEX_GRAPH_ERROR",
    "APEX_GRAPH_COMPILE_EXCEPTION",
    "APEX_GRAPH_COMPILE_ERRORS",
    "APEX_GRAPH_OUTPUT_UNCONNECTED",
    "KINEFX_DUPLICATE_JOINT_NAMES",
    "KINEFX_PARENT_CYCLE",
}

GROUP_PARM_TOKENS = ("group", "constraintgroup", "pointgroup", "primgroup")
TIME_TOKENS_RE = re.compile(r"(?:\$F(?:F|START|END)?|@Frame\b|@Time\b|hou\.frame\s*\()")
SOP_LOCAL_CONTEXT_RE = re.compile(
    r"(?:\$(?:PT|PR|VTX|NPT|NPR|NVTX|BBX|BBY|BBZ|TX|TY|TZ|CR|CG|CB|CA)\b|@[A-Za-z_]|\b(?:point|prim|vertex)\s*\(\s*0\s*,\s*\$)",
    re.IGNORECASE,
)
ATTRIBUTE_REF_RE = re.compile(r"@([A-Za-z_][A-Za-z0-9_]*)")
FRAME_TOKEN_RE = re.compile(r"(?:\$F\d*|#+|<UDIM>|%\d*d)", re.IGNORECASE)
PATH_EXT_RE = re.compile(
    r"\.(?:bgeo(?:\.sc)?|abc|fbx|usd[ac]?|hip(?:nc|lc)?|obj|vdb|json|csv|txt|png|exr|jpg|rat|hda|otl)$",
    re.IGNORECASE,
)
INTERNAL_HIGH_SIGNAL_RE = re.compile(
    r"(?:emergency limit|trying to scatter\s+\d+\s+points|generating\s+\d+\s+points|"
    r"unable to evaluate expression|compile(?:d|r)?\s+(?:error|failed)|nan\b|infinite value|"
    r"non[- ]?manifold|invalid geometry|singular transform)",
    re.IGNORECASE,
)
INTERNAL_MESSAGE_NODE_TOKENS = (
    "scatter",
    "compile",
    "doctor",
    "validate",
    "error",
    "fracture",
    "boolean",
    "rewire",
    "graph",
)
MESSAGE_NODE_PATH_RE = re.compile(r"\((/[^()]+?)/[^/()]+\)")


def _now_iso() -> str:
    return _datetime.datetime.now().astimezone().isoformat(timespec="seconds")


def _safe(func: Callable[[], Any], default: Any = None) -> Any:
    try:
        return func()
    except Exception:
        return default


def _plain(value: Any, limit: int = 1000) -> Any:
    if value is None or isinstance(value, (bool, int, float)):
        return value
    if isinstance(value, str):
        return value if len(value) <= limit else value[:limit] + "..."
    if isinstance(value, dict):
        return {str(key): _plain(item, limit) for key, item in list(value.items())[:100]}
    if isinstance(value, (list, tuple, set)):
        return [_plain(item, limit) for item in list(value)[:100]]
    try:
        return _plain(tuple(value), limit)
    except Exception:
        text = str(value)
        return text if len(text) <= limit else text[:limit] + "..."


def _hash_values(values: Sequence[Any]) -> str:
    prepared = [_plain(value, 10_000) for value in values]
    try:
        prepared = sorted(prepared, key=lambda item: json.dumps(item, ensure_ascii=False, sort_keys=True))
    except Exception:
        pass
    payload = json.dumps(prepared, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return hashlib.sha1(payload.encode("utf-8", "replace")).hexdigest()[:16]


def _node_path(node: Any) -> str:
    return str(_safe(lambda: node.path(), "") or "")


def _node_type_name(node: Any) -> str:
    return str(_safe(lambda: node.type().name(), "") or "")


def _node_description(node: Any) -> str:
    return str(_safe(lambda: node.type().description(), "") or "")


def _node_category(node: Any) -> str:
    return str(_safe(lambda: node.type().category().name(), "") or "")


def _node_type_text(node: Any) -> str:
    return (_node_type_name(node) + " " + _node_description(node)).lower()


def _is_sop(node: Any) -> bool:
    if hou is None:
        return False
    return isinstance(node, getattr(hou, "SopNode", object))


def _is_rbd_node(node: Any) -> bool:
    text = _node_type_text(node)
    return any(token in text for token in RBD_TYPE_HINTS)


def _is_apex_node(node: Any) -> bool:
    text = _node_type_text(node)
    return any(token in text for token in APEX_TYPE_HINTS)


def _is_kinefx_node(node: Any) -> bool:
    text = _node_type_text(node)
    return any(token in text for token in KINEFX_TYPE_HINTS)


def _is_cache_node(node: Any) -> bool:
    text = _node_type_text(node)
    return any(token in text for token in CACHE_TYPE_HINTS)


def _is_attribute_node(node: Any) -> bool:
    text = _node_type_text(node)
    return any(token in text for token in ATTRIBUTE_NODE_HINTS)


def _value_is_finite(value: Any) -> bool:
    if isinstance(value, bool):
        return True
    if isinstance(value, (int, float)):
        return math.isfinite(float(value))
    if isinstance(value, (tuple, list)):
        return all(_value_is_finite(item) for item in value)
    return True


def _vector_length(value: Any) -> Optional[float]:
    if not isinstance(value, (tuple, list)) or not value:
        return None
    if not all(isinstance(item, (int, float)) for item in value):
        return None
    try:
        return math.sqrt(sum(float(item) * float(item) for item in value))
    except Exception:
        return None


def _bbox_record(bbox: Any) -> Dict[str, Any]:
    if bbox is None:
        return {}
    minimum = _safe(lambda: tuple(bbox.minvec()), ())
    maximum = _safe(lambda: tuple(bbox.maxvec()), ())
    size = _safe(lambda: tuple(bbox.sizevec()), ())
    center = _safe(lambda: tuple(bbox.center()), ())
    diagonal = _vector_length(size) or 0.0
    return {
        "min": _plain(minimum),
        "max": _plain(maximum),
        "size": _plain(size),
        "center": _plain(center),
        "diagonal": diagonal,
    }


@dataclass
class Issue:
    rule_id: str
    severity: str
    confidence: str
    profile: str
    node_path: str
    summary: str
    evidence: Dict[str, Any] = field(default_factory=dict)
    suggestion: str = ""
    symptoms: List[str] = field(default_factory=list)
    related_nodes: List[str] = field(default_factory=list)

    def score(self, symptom: str = "auto") -> int:
        value = SEVERITY_SCORE.get(self.severity, 0) + CONFIDENCE_SCORE.get(self.confidence, 0)
        if symptom != "auto" and symptom in self.symptoms:
            value += 80
        return value

    def to_dict(self) -> Dict[str, Any]:
        return {
            "rule_id": self.rule_id,
            "severity": self.severity,
            "severity_ja": SEVERITY_LABEL_JA.get(self.severity, self.severity),
            "confidence": self.confidence,
            "profile": self.profile,
            "node_path": self.node_path,
            "summary": self.summary,
            "evidence": _plain(self.evidence, 10_000),
            "suggestion": self.suggestion,
            "symptoms": list(self.symptoms),
            "related_nodes": list(self.related_nodes),
            "llm_state": "fail" if self.rule_id in LLM_FAIL_RULES and self.confidence == "high" else "review",
        }


@dataclass
class CheckResult:
    check_id: str
    status: str
    profile: str
    node_path: str
    evidence: Dict[str, Any] = field(default_factory=dict)
    note: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {
            "check_id": self.check_id,
            "status": self.status,
            "profile": self.profile,
            "node_path": self.node_path,
            "evidence": _plain(self.evidence, 10_000),
            "note": self.note,
        }


@dataclass
class AttributeStats:
    owner: str
    name: str
    data_type: str
    tuple_size: int
    count: int
    sampled: int
    unique_count: Optional[int]
    duplicate_count: Optional[int]
    empty_count: int
    nonfinite_count: int
    negative_count: int
    zero_count: int
    positive_count: int
    minimum: Optional[float]
    maximum: Optional[float]
    vector_max_length: Optional[float]
    fingerprint: str
    sample: List[Any]
    values: List[Any] = field(default_factory=list, repr=False)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "owner": self.owner,
            "name": self.name,
            "data_type": self.data_type,
            "tuple_size": self.tuple_size,
            "count": self.count,
            "sampled": self.sampled,
            "unique_count": self.unique_count,
            "duplicate_count": self.duplicate_count,
            "empty_count": self.empty_count,
            "nonfinite_count": self.nonfinite_count,
            "negative_count": self.negative_count,
            "zero_count": self.zero_count,
            "positive_count": self.positive_count,
            "minimum": self.minimum,
            "maximum": self.maximum,
            "vector_max_length": self.vector_max_length,
            "fingerprint": self.fingerprint,
            "sample": _plain(self.sample),
        }


@dataclass
class GeometrySnapshot:
    key: str
    node_path: str
    output_index: int
    frame: float
    valid: Optional[bool]
    counts: Dict[str, int]
    bbox: Dict[str, Any]
    attributes: Dict[str, Dict[str, Dict[str, Any]]]
    stats: Dict[str, AttributeStats]
    groups: Dict[str, Dict[str, int]]
    packed_paths: List[str]
    primitive_pairs: List[Tuple[str, str]]
    primitive_min_dimensions: List[float]
    primitive_diagonals: List[float]
    degenerate_primitives: int
    nonmanifold_edges: int
    packed_bad_transforms: int
    packed_primitive_count: int
    polygon_primitive_count: int
    closed_polygon_primitive_count: int
    open_polyline_primitive_count: int
    two_endpoint_open_line_count: int
    primitive_role_sampled: int
    skeleton_edges: List[Tuple[int, int]]
    errors: List[str]

    def stat(self, owner: str, name: str) -> Optional[AttributeStats]:
        return self.stats.get(owner + ":" + name)

    def any_stat(self, name: str) -> Optional[AttributeStats]:
        for owner in ("point", "primitive", "vertex", "global"):
            found = self.stat(owner, name)
            if found is not None:
                return found
        return None

    def attribute_owner(self, name: str) -> Optional[str]:
        for owner, attrs in self.attributes.items():
            if name in attrs:
                return owner
        return None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "key": self.key,
            "node_path": self.node_path,
            "output_index": self.output_index,
            "frame": self.frame,
            "valid": self.valid,
            "counts": dict(self.counts),
            "bbox": _plain(self.bbox),
            "attributes": _plain(self.attributes),
            "attribute_stats": {key: value.to_dict() for key, value in sorted(self.stats.items())},
            "groups": _plain(self.groups),
            "packed_paths": list(self.packed_paths[:200]),
            "packed_path_count": len(self.packed_paths),
            "constraint_pair_count": len(self.primitive_pairs),
            "primitive_min_dimension_sample": _plain(self.primitive_min_dimensions[:50]),
            "primitive_diagonal_sample": _plain(self.primitive_diagonals[:50]),
            "degenerate_primitives": self.degenerate_primitives,
            "nonmanifold_edges": self.nonmanifold_edges,
            "packed_bad_transforms": self.packed_bad_transforms,
            "packed_primitive_count": self.packed_primitive_count,
            "polygon_primitive_count": self.polygon_primitive_count,
            "closed_polygon_primitive_count": self.closed_polygon_primitive_count,
            "open_polyline_primitive_count": self.open_polyline_primitive_count,
            "two_endpoint_open_line_count": self.two_endpoint_open_line_count,
            "primitive_role_sampled": self.primitive_role_sampled,
            "primitive_role_complete": self.primitive_role_sampled == self.counts.get("primitives", 0),
            "skeleton_edge_count": len(self.skeleton_edges),
            "errors": list(self.errors),
        }


def _attribute_metadata(attrib: Any) -> Dict[str, Any]:
    return {
        "data_type": str(_safe(lambda: attrib.dataType(), "")),
        "numeric_data_type": str(_safe(lambda: attrib.numericDataType(), "")),
        "size": int(_safe(lambda: attrib.size(), 1) or 1),
        "is_array": bool(_safe(lambda: attrib.isArrayType(), False)),
        "qualifier": _plain(_safe(lambda: attrib.qualifier(), None)),
    }


def _geometry_elements(geometry: Any, owner: str) -> Sequence[Any]:
    if owner == "point":
        return _safe(lambda: geometry.points(), ()) or ()
    if owner == "primitive":
        return _safe(lambda: geometry.prims(), ()) or ()
    if owner == "vertex":
        return _safe(lambda: geometry.iterVertices(), ()) or ()
    return ()


def _attribute_values(
    geometry: Any,
    attrib: Any,
    owner: str,
    exact_strings: bool,
    limit: int,
) -> Tuple[List[Any], int]:
    name = str(_safe(lambda: attrib.name(), "") or "")
    data_type = str(_safe(lambda: attrib.dataType(), "") or "").lower()
    elements = _geometry_elements(geometry, owner)
    total = len(elements) if hasattr(elements, "__len__") else 0

    if "string" in data_type and owner in ("point", "primitive"):
        method_name = "pointStringAttribValues" if owner == "point" else "primStringAttribValues"
        method = getattr(geometry, method_name, None)
        if callable(method):
            values = _safe(lambda: list(method(name)), None)
            if values is not None:
                if exact_strings:
                    return values, len(values)
                return values[:limit], len(values)

    values: List[Any] = []
    for index, element in enumerate(elements):
        if index >= limit:
            break
        value = _safe(lambda element=element: element.attribValue(attrib), None)
        values.append(_plain(value, 10_000))
    return values, total


def _make_attribute_stats(
    geometry: Any,
    attrib: Any,
    owner: str,
    exact_strings: bool = False,
    limit: int = 20_000,
) -> AttributeStats:
    name = str(_safe(lambda: attrib.name(), "") or "")
    data_type = str(_safe(lambda: attrib.dataType(), "") or "")
    tuple_size = int(_safe(lambda: attrib.size(), 1) or 1)
    values, total = _attribute_values(geometry, attrib, owner, exact_strings, limit)
    unique_count: Optional[int] = None
    duplicate_count: Optional[int] = None
    empty_count = 0
    nonfinite_count = 0
    negative_count = 0
    zero_count = 0
    positive_count = 0
    scalar_values: List[float] = []
    vector_lengths: List[float] = []

    hashable_values: List[Any] = []
    for value in values:
        if isinstance(value, str):
            if value == "":
                empty_count += 1
            hashable_values.append(value)
        elif isinstance(value, (int, float)) and not isinstance(value, bool):
            number = float(value)
            if math.isfinite(number):
                scalar_values.append(number)
                if number < 0:
                    negative_count += 1
                elif number > 0:
                    positive_count += 1
                else:
                    zero_count += 1
            else:
                nonfinite_count += 1
            hashable_values.append(number)
        elif isinstance(value, (tuple, list)):
            if not _value_is_finite(value):
                nonfinite_count += 1
            length = _vector_length(value)
            if length is not None and math.isfinite(length):
                vector_lengths.append(length)
            hashable_values.append(tuple(value))
        else:
            hashable_values.append(str(value))

    try:
        unique_count = len(set(hashable_values))
        duplicate_count = max(0, len(hashable_values) - unique_count)
    except Exception:
        pass

    return AttributeStats(
        owner=owner,
        name=name,
        data_type=data_type,
        tuple_size=tuple_size,
        count=total,
        sampled=len(values),
        unique_count=unique_count,
        duplicate_count=duplicate_count,
        empty_count=empty_count,
        nonfinite_count=nonfinite_count,
        negative_count=negative_count,
        zero_count=zero_count,
        positive_count=positive_count,
        minimum=min(scalar_values) if scalar_values else None,
        maximum=max(scalar_values) if scalar_values else None,
        vector_max_length=max(vector_lengths) if vector_lengths else None,
        fingerprint=_hash_values(hashable_values),
        sample=list(values[:8]),
        values=list(values),
    )


def _group_count(group: Any, owner: str) -> int:
    method_name = {
        "point": "points",
        "primitive": "prims",
        "vertex": "vertices",
        "edge": "edges",
    }.get(owner)
    if not method_name:
        return 0
    return len(_safe(lambda: getattr(group, method_name)(), ()) or ())


def _matrix_determinant(value: Any) -> Optional[float]:
    if hou is None:
        return None
    try:
        if isinstance(value, hou.Matrix4):
            return float(value.determinant())
        if isinstance(value, hou.Matrix3):
            return float(value.determinant())
        sequence = tuple(value)
        if len(sequence) == 16:
            return float(hou.Matrix4(sequence).determinant())
        if len(sequence) == 9:
            return float(hou.Matrix3(sequence).determinant())
    except Exception:
        return None
    return None


def build_geometry_snapshot(
    geometry: Any,
    key: str,
    node_path: str,
    output_index: int,
    frame: float,
    deep: bool = False,
) -> GeometrySnapshot:
    errors: List[str] = []
    if geometry is None:
        raise RuntimeError("No geometry was returned")

    points = _safe(lambda: geometry.points(), ()) or ()
    primitives = _safe(lambda: geometry.prims(), ()) or ()
    counts = {
        "points": len(points),
        "primitives": len(primitives),
        "vertices": int(_safe(lambda: geometry.intrinsicValue("vertexcount"), 0) or 0),
    }
    if not counts["vertices"]:
        counts["vertices"] = sum(int(_safe(lambda prim=prim: prim.numVertices(), 0) or 0) for prim in primitives)

    attributes: Dict[str, Dict[str, Dict[str, Any]]] = {
        "point": {},
        "primitive": {},
        "vertex": {},
        "global": {},
    }
    stats: Dict[str, AttributeStats] = {}
    owner_methods = {
        "point": "pointAttribs",
        "primitive": "primAttribs",
        "vertex": "vertexAttribs",
        "global": "globalAttribs",
    }
    for owner, method_name in owner_methods.items():
        attribs = _safe(lambda method_name=method_name: getattr(geometry, method_name)(), ()) or ()
        for attrib in attribs:
            name = str(_safe(lambda attrib=attrib: attrib.name(), "") or "")
            if not name:
                continue
            attributes[owner][name] = _attribute_metadata(attrib)
            if name in WATCH_ATTRIBUTES or name.lower() in {item.lower() for item in WATCH_ATTRIBUTES}:
                exact = name in IDENTITY_ATTRIBUTES and owner in ("point", "primitive")
                limit = 250_000 if exact else (100_000 if deep else 20_000)
                try:
                    stats[owner + ":" + name] = _make_attribute_stats(
                        geometry,
                        attrib,
                        owner,
                        exact_strings=exact,
                        limit=limit,
                    )
                except Exception as exc:
                    errors.append("Attribute %s:%s: %s" % (owner, name, exc))

    groups: Dict[str, Dict[str, int]] = {"point": {}, "primitive": {}, "vertex": {}, "edge": {}}
    group_methods = {
        "point": "pointGroups",
        "primitive": "primGroups",
        "vertex": "vertexGroups",
        "edge": "edgeGroups",
    }
    for owner, method_name in group_methods.items():
        for group in _safe(lambda method_name=method_name: getattr(geometry, method_name)(), ()) or ():
            name = str(_safe(lambda group=group: group.name(), "") or "")
            if name:
                groups[owner][name] = _group_count(group, owner)

    packed_paths: List[str] = []
    extract_packed_paths = getattr(geometry, "extractPackedPaths", None)
    if callable(extract_packed_paths):
        raw_paths = _safe(lambda: extract_packed_paths("*"), ()) or ()
        packed_paths = sorted({str(value).replace("\\", "/") for value in raw_paths if str(value or "").strip()})

    point_name_attrib = _safe(lambda: geometry.findPointAttrib("name"), None)
    primitive_pairs: List[Tuple[str, str]] = []
    skeleton_edges: List[Tuple[int, int]] = []
    if point_name_attrib is not None:
        for prim in primitives[:250_000]:
            prim_points = _safe(lambda prim=prim: prim.points(), ()) or ()
            if len(prim_points) >= 2:
                for left_point, right_point in zip(prim_points[:-1], prim_points[1:]):
                    left_index = int(_safe(lambda left_point=left_point: left_point.number(), -1))
                    right_index = int(_safe(lambda right_point=right_point: right_point.number(), -1))
                    if left_index >= 0 and right_index >= 0:
                        skeleton_edges.append((left_index, right_index))
                if len(prim_points) == 2:
                    left = str(_safe(lambda: prim_points[0].attribValue(point_name_attrib), "") or "")
                    right = str(_safe(lambda: prim_points[1].attribValue(point_name_attrib), "") or "")
                    primitive_pairs.append((left, right))

    primitive_min_dimensions: List[float] = []
    primitive_diagonals: List[float] = []
    packed_bad_transforms = 0
    packed_primitive_count = 0
    polygon_primitive_count = 0
    closed_polygon_primitive_count = 0
    open_polyline_primitive_count = 0
    two_endpoint_open_line_count = 0
    primitive_role_limit = 250_000 if deep else 20_000
    primitive_role_sampled = min(len(primitives), primitive_role_limit)
    for prim in primitives[:primitive_role_limit]:
        bbox = _safe(lambda prim=prim: prim.boundingBox(), None)
        if bbox is not None:
            size = tuple(_safe(lambda bbox=bbox: bbox.sizevec(), ()) or ())
            positive = [abs(float(item)) for item in size if abs(float(item)) > 1e-12]
            if positive:
                primitive_min_dimensions.append(min(positive))
            diagonal = _vector_length(size)
            if diagonal is not None:
                primitive_diagonals.append(diagonal)
        type_name = str(_safe(lambda prim=prim: prim.type().name(), "") or "").lower()
        if "packed" in type_name:
            packed_primitive_count += 1
            transform = _safe(lambda prim=prim: prim.fullTransform(), None)
            determinant = _matrix_determinant(transform)
            if determinant is not None and (not math.isfinite(determinant) or abs(determinant) < 1e-12):
                packed_bad_transforms += 1
        if "poly" in type_name:
            polygon_primitive_count += 1
            prim_points = _safe(lambda prim=prim: prim.points(), ()) or ()
            is_closed = bool(_safe(lambda prim=prim: prim.isClosed(), False))
            if is_closed:
                closed_polygon_primitive_count += 1
            else:
                open_polyline_primitive_count += 1
                if len(prim_points) == 2 and point_name_attrib is not None:
                    two_endpoint_open_line_count += 1

    degenerate_primitives = 0
    nonmanifold_edges = 0
    if deep:
        edge_counts: Dict[Tuple[int, int], int] = {}
        for prim in primitives[:250_000]:
            prim_points = _safe(lambda prim=prim: prim.points(), ()) or ()
            type_name = str(_safe(lambda prim=prim: prim.type().name(), "") or "").lower()
            if "poly" in type_name:
                # Open polygons are curves/constraint polylines, not surface
                # faces.  Their measured area is expected to be zero.
                if not bool(_safe(lambda prim=prim: prim.isClosed(), False)):
                    continue
                indices = [int(_safe(lambda point=point: point.number(), -1)) for point in prim_points]
                is_degenerate = len(prim_points) < 3 or len(set(indices)) < 3
                area = _safe(lambda prim=prim: prim.intrinsicValue("measuredarea"), None)
                if isinstance(area, (int, float)) and abs(float(area)) < 1e-14:
                    is_degenerate = True
                if is_degenerate:
                    degenerate_primitives += 1
                if len(indices) >= 2:
                    loop = indices + [indices[0]]
                    for left, right in zip(loop[:-1], loop[1:]):
                        if left < 0 or right < 0 or left == right:
                            continue
                        edge = (min(left, right), max(left, right))
                        edge_counts[edge] = edge_counts.get(edge, 0) + 1
        nonmanifold_edges = sum(1 for count in edge_counts.values() if count > 2)

    return GeometrySnapshot(
        key=key,
        node_path=node_path,
        output_index=output_index,
        frame=frame,
        valid=_safe(lambda: geometry.isValid(), None),
        counts=counts,
        bbox=_bbox_record(_safe(lambda: geometry.boundingBox(), None)),
        attributes=attributes,
        stats=stats,
        groups=groups,
        packed_paths=packed_paths,
        primitive_pairs=primitive_pairs,
        primitive_min_dimensions=primitive_min_dimensions,
        primitive_diagonals=primitive_diagonals,
        degenerate_primitives=degenerate_primitives,
        nonmanifold_edges=nonmanifold_edges,
        packed_bad_transforms=packed_bad_transforms,
        packed_primitive_count=packed_primitive_count,
        polygon_primitive_count=polygon_primitive_count,
        closed_polygon_primitive_count=closed_polygon_primitive_count,
        open_polyline_primitive_count=open_polyline_primitive_count,
        two_endpoint_open_line_count=two_endpoint_open_line_count,
        primitive_role_sampled=primitive_role_sampled,
        skeleton_edges=skeleton_edges,
        errors=errors,
    )


def _selected_with_hops(nodes: Sequence[Any], hops: int) -> List[Any]:
    result: Dict[str, Any] = {_node_path(node): node for node in nodes if _node_path(node)}
    frontier = list(result.values())
    for _index in range(max(0, hops)):
        next_frontier: List[Any] = []
        for node in frontier:
            neighbors = list(_safe(lambda node=node: node.inputs(), ()) or ())
            neighbors.extend(list(_safe(lambda node=node: node.outputs(), ()) or ()))
            for neighbor in neighbors:
                path = _node_path(neighbor)
                if path and path not in result:
                    result[path] = neighbor
                    next_frontier.append(neighbor)
        frontier = next_frontier
    return sorted(result.values(), key=_node_path)


def resolve_scope(scope: str) -> List[Any]:
    if hou is None:
        raise RuntimeError("This tool must run inside Houdini")
    selected = list(hou.selectedNodes())
    if not selected:
        return []
    if scope == "selected_plus_one":
        return _selected_with_hops(selected, 1)
    if scope == "selected_plus_two":
        return _selected_with_hops(selected, 2)
    if scope == "network":
        parents = {_node_path(node.parent()): node.parent() for node in selected}
        nodes: Dict[str, Any] = {}
        for parent in parents.values():
            for child in _safe(lambda parent=parent: parent.children(), ()) or ():
                nodes[_node_path(child)] = child
        return sorted(nodes.values(), key=_node_path)
    return sorted(selected, key=_node_path)


class HoudiniNetworkAnalyzer:
    def __init__(
        self,
        nodes: Sequence[Any],
        profile: str = "auto",
        scan_level: str = "standard",
        symptom: str = "auto",
        compare_frames: Optional[Sequence[float]] = None,
        progress: Optional[Callable[[str, int, int], None]] = None,
    ) -> None:
        self.nodes = sorted({node for node in nodes if node is not None}, key=_node_path)
        self.profile = profile
        self.scan_level = scan_level
        self.symptom = symptom
        self.compare_frames = list(compare_frames or [])[:6]
        self.progress = progress
        self.issues: List[Issue] = []
        self._issue_keys: Set[Tuple[str, str, str]] = set()
        self.checks: List[CheckResult] = []
        self._check_keys: Set[Tuple[str, str, str]] = set()
        self.snapshots: Dict[str, GeometrySnapshot] = {}
        self._snapshot_cache: Dict[Tuple[str, int, float], GeometrySnapshot] = {}
        self.node_records: Dict[str, Dict[str, Any]] = {}
        self.time_dependent_nodes: Set[str] = set()
        self.scan_notes: List[str] = []
        self.original_frame = float(hou.frame()) if hou is not None else 1.0
        self.start_frame = float(_safe(lambda: hou.playbar.frameRange()[0], 1.0)) if hou is not None else 1.0

    def _emit_progress(self, text: str, index: int, total: int) -> None:
        if self.progress is not None:
            self.progress(text, index, total)

    def add_issue(
        self,
        rule_id: str,
        severity: str,
        confidence: str,
        profile: str,
        node_path: str,
        summary: str,
        evidence: Optional[Dict[str, Any]] = None,
        suggestion: str = "",
        symptoms: Optional[Sequence[str]] = None,
        related_nodes: Optional[Sequence[str]] = None,
    ) -> None:
        key = (rule_id, node_path, summary)
        if key in self._issue_keys:
            return
        self._issue_keys.add(key)
        self.issues.append(
            Issue(
                rule_id=rule_id,
                severity=severity,
                confidence=confidence,
                profile=profile,
                node_path=node_path,
                summary=summary,
                evidence=evidence or {},
                suggestion=suggestion,
                symptoms=list(symptoms or []),
                related_nodes=list(related_nodes or []),
            )
        )

    def add_check(
        self,
        check_id: str,
        status: str,
        profile: str,
        node_path: str,
        evidence: Optional[Dict[str, Any]] = None,
        note: str = "",
    ) -> None:
        context = str((evidence or {}).get("context", ""))
        key = (check_id, node_path, context)
        if key in self._check_keys:
            return
        self._check_keys.add(key)
        self.checks.append(
            CheckResult(
                check_id=check_id,
                status=status,
                profile=profile,
                node_path=node_path,
                evidence=evidence or {},
                note=note,
            )
        )

    def analyze(self) -> Dict[str, Any]:
        if hou is None:
            raise RuntimeError("This analyzer must run inside Houdini")
        if not self.nodes:
            raise RuntimeError("解析対象ノードが選択されていません")

        total = len(self.nodes)
        try:
            for index, node in enumerate(self.nodes, 1):
                self._emit_progress("ネットワーク検査: " + _node_path(node), index, total)
                self.node_records[_node_path(node)] = self._node_record(node)
                self._diagnose_static_node(node)

            if self.scan_level != "fast":
                self._collect_main_snapshots()
                self._diagnose_top_level_messages()
                self._diagnose_high_signal_internal_messages()
                self._diagnose_attribute_lineage()
                self._diagnose_identity_empty_transitions()
                self._diagnose_group_parameters()

            self._diagnose_rbd_profiles()
            self._diagnose_apex_profiles()
            self._diagnose_cache_boundaries()

            if self.scan_level == "deep" and self.compare_frames:
                self._diagnose_frame_differences()
        finally:
            if hou is not None and abs(float(hou.frame()) - self.original_frame) > 1e-6:
                _safe(lambda: hou.setFrame(self.original_frame), None)

        ordered = sorted(
            self.issues,
            key=lambda issue: (-issue.score(self.symptom), issue.node_path, issue.rule_id),
        )
        report = {
            "schema": SCHEMA,
            "tool": {"name": TOOL_NAME, "version": VERSION, "created_at": _now_iso()},
            "scene": {
                "hip_file": _safe(lambda: hou.hipFile.path(), ""),
                "houdini_version": _safe(lambda: hou.applicationVersionString(), ""),
                "frame": self.original_frame,
                "start_frame": self.start_frame,
            },
            "options": {
                "profile": self.profile,
                "scan_level": self.scan_level,
                "symptom": self.symptom,
                "compare_frames": self.compare_frames,
            },
            "summary": self._summary(ordered),
            "nodes": [self.node_records[path] for path in sorted(self.node_records)],
            "issues": [issue.to_dict() for issue in ordered],
            "checks": [check.to_dict() for check in sorted(self.checks, key=lambda item: (item.status, item.node_path, item.check_id))],
            "snapshots": {key: value.to_dict() for key, value in sorted(self.snapshots.items())},
            "notes": list(self.scan_notes),
        }
        return report

    def _summary(self, issues: Sequence[Issue]) -> Dict[str, Any]:
        counts = {key: 0 for key in SEVERITY_SCORE}
        profiles: Dict[str, int] = {}
        for issue in issues:
            counts[issue.severity] = counts.get(issue.severity, 0) + 1
            profiles[issue.profile] = profiles.get(issue.profile, 0) + 1
        return {
            "node_count": len(self.nodes),
            "issue_count": len(issues),
            "severity_counts": counts,
            "profile_counts": profiles,
            "geometry_snapshot_count": len(self.snapshots),
            "time_dependent_node_count": len(self.time_dependent_nodes),
            "check_count": len(self.checks),
            "check_status_counts": {
                status: sum(1 for check in self.checks if check.status == status)
                for status in ("pass", "fail", "review", "not_checked")
            },
        }

    def _node_record(self, node: Any) -> Dict[str, Any]:
        connections = []
        for connection in _safe(lambda: node.inputConnections(), ()) or ():
            connections.append(
                {
                    "input_index": int(_safe(lambda connection=connection: connection.inputIndex(), -1)),
                    "source_node": _node_path(_safe(lambda connection=connection: connection.inputNode(), None)),
                    "source_output": int(_safe(lambda connection=connection: connection.outputIndex(), 0) or 0),
                }
            )
        flags = {
            "bypassed": bool(_safe(lambda: node.isBypassed(), False)),
            "display": bool(_safe(lambda: node.isDisplayFlagSet(), False)),
            "render": bool(_safe(lambda: node.isRenderFlagSet(), False)),
            "locked": bool(_safe(lambda: node.isLockedHDA(), False)),
        }
        return {
            "path": _node_path(node),
            "name": str(_safe(lambda: node.name(), "") or ""),
            "type": _node_type_name(node),
            "description": _node_description(node),
            "category": _node_category(node),
            "flags": flags,
            "inputs": connections,
            "outputs": [_node_path(item) for item in (_safe(lambda: node.outputs(), ()) or ())],
            "comment": str(_safe(lambda: node.comment(), "") or ""),
        }

    def _diagnose_static_node(self, node: Any) -> None:
        path = _node_path(node)
        node_type = _node_type_name(node)

        if bool(_safe(lambda: node.isBypassed(), False)):
            self.add_issue(
                "NODE_BYPASSED",
                "info",
                "high",
                "general",
                path,
                "ノードがBypassされています",
                suggestion="意図した比較枝でなければBypass状態を確認してください。",
            )

        minimum_inputs = int(_safe(lambda: node.type().minNumInputs(), 0) or 0)
        inputs = list(_safe(lambda: node.inputs(), ()) or ())
        missing = [index for index in range(minimum_inputs) if index >= len(inputs) or inputs[index] is None]
        if missing:
            self.add_issue(
                "NODE_REQUIRED_INPUT_MISSING",
                "error",
                "high",
                "general",
                path,
                "必須入力が接続されていません",
                {"node_type": node_type, "missing_input_indices_zero_based": missing},
                "ノードの入力ラベルと接続元を確認してください。",
                ["apex_graph", "rbd_general"],
            )

        time_dependent = False
        for parm in _safe(lambda: node.parms(), ()) or ():
            parm_name = str(_safe(lambda parm=parm: parm.name(), "") or "")
            expression = ""
            if bool(_safe(lambda parm=parm: parm.isTimeDependent(), False)):
                time_dependent = True
            if int(_safe(lambda parm=parm: len(parm.keyframes()), 0) or 0) > 0:
                expression = str(_safe(lambda parm=parm: parm.expression(), "") or "")
                if expression and TIME_TOKENS_RE.search(expression):
                    time_dependent = True
                if expression and not SOP_LOCAL_CONTEXT_RE.search(expression):
                    try:
                        parm.eval()
                    except Exception as exc:
                        self.add_issue(
                            "PARM_EXPRESSION_EVALUATION_FAILED",
                            "error",
                            "high",
                            "general",
                            path,
                            "パラメータ式を評価できません: " + parm_name,
                            {"expression": expression, "error": str(exc)},
                            "削除済みチャンネルや存在しないノード参照を確認してください。",
                        )
            self._diagnose_file_parameter(node, parm)

        if time_dependent:
            self.time_dependent_nodes.add(path)

    def _diagnose_top_level_messages(self) -> None:
        # Read messages after geometry snapshots have cooked the selected SOPs.
        # Reading Attribute Create errors before its per-element cook can turn
        # valid $PT/$PR expressions into transient "Undefined variable" text.
        for node in self.nodes:
            if self._main_snapshot_for_node(node) is None and _is_sop(node):
                continue
            self._record_node_messages(node)

    def _message_owner_path(self, message: str, fallback: str) -> str:
        match = MESSAGE_NODE_PATH_RE.search(message)
        if match is None:
            return fallback
        candidate = match.group(1)
        if hou is not None and _safe(lambda: hou.node(candidate), None) is not None:
            return candidate
        return fallback

    def _record_node_messages(self, node: Any) -> None:
        observed_on = _node_path(node)
        for message in list(_safe(lambda: node.errors(), ()) or ()):
            text = str(message)
            owner_path = self._message_owner_path(text, observed_on)
            self.add_issue(
                "HOUDINI_NODE_ERROR",
                "error",
                "high",
                "houdini",
                owner_path,
                "HoudiniがCookエラーを報告しました",
                {"message": text, "observed_on": observed_on},
                "記載された式または内部ノードを再Cookし、同じエラーが単独で再現するか確認してください。",
                related_nodes=[] if owner_path == observed_on else [observed_on],
            )
        for message in list(_safe(lambda: node.warnings(), ()) or ()):
            text = str(message)
            mismatch = "mis-match of attributes" in text.lower() or "mismatch of attributes" in text.lower()
            self.add_issue(
                "HOUDINI_ATTRIBUTE_MISMATCH_NOTICE" if mismatch else "HOUDINI_NODE_WARNING",
                "notice" if mismatch else "warning",
                "medium" if mismatch else "high",
                "houdini",
                observed_on,
                "Houdiniが入力属性差を報告しました" if mismatch else "HoudiniがCook警告を報告しました",
                {"message": text},
                "属性差の警告だけでは不具合を確定しません。Solver入力で必要な属性値とname契約を別に確認してください。"
                if mismatch
                else "同じ警告が最終出力Cookでも再現するか確認してください。",
            )

    def _diagnose_file_parameter(self, node: Any, parm: Any) -> None:
        name = str(_safe(lambda: parm.name(), "") or "")
        label = str(_safe(lambda: parm.parmTemplate().label(), "") or "")
        token = (name + " " + label).lower()
        if not any(item in token for item in ("file", "path", "cache", "geometry", "filename")):
            return
        raw = _safe(lambda: parm.unexpandedString(), None)
        if not isinstance(raw, str) or not raw.strip() or raw.startswith("op:"):
            return
        if not PATH_EXT_RE.search(raw) or FRAME_TOKEN_RE.search(raw):
            return
        expanded = str(_safe(lambda: hou.expandString(raw), raw) if hou is not None else raw)
        normalized = os.path.normpath(expanded)
        is_output = any(item in token for item in ("output", "save", "sopoutput", "cache"))
        if is_output:
            # Output directories are often created only when a ROP/cache is
            # executed.  Reporting them during an ordinary network scan causes
            # noise, so missing output folders are checked only by explicit
            # cache rules when Load from Disk is enabled.
            return
        elif not os.path.exists(normalized):
            self.add_issue(
                "FILE_INPUT_MISSING",
                "error",
                "high",
                "general",
                _node_path(node),
                "参照ファイルが存在しません",
                {"parameter": name, "path": normalized},
                "パス、環境変数、相対パスの基準を確認してください。",
            )

    def _should_snapshot_node(self, node: Any) -> bool:
        if not _is_sop(node):
            return False
        if self.scan_level == "deep":
            return True
        text = _node_type_text(node)
        if _is_rbd_node(node) or _is_apex_node(node) or _is_kinefx_node(node):
            return True
        if _is_attribute_node(node) or _is_cache_node(node):
            return True
        if any(token in text for token in ("null", "output", "pack", "unpack", "switch", "blast", "clean", "polydoctor", "fuse")):
            return True
        if bool(_safe(lambda: node.isDisplayFlagSet(), False)) or bool(_safe(lambda: node.isRenderFlagSet(), False)):
            return True
        selected_paths = {_node_path(item) for item in self.nodes}
        inputs = [_node_path(item) for item in (_safe(lambda: node.inputs(), ()) or ()) if item is not None]
        outputs = [_node_path(item) for item in (_safe(lambda: node.outputs(), ()) or ()) if item is not None]
        return any(path not in selected_paths for path in inputs + outputs)

    def _snapshot_key(self, node_path: str, output_index: int, frame: float, suffix: str = "") -> str:
        frame_text = ("%.3f" % frame).rstrip("0").rstrip(".")
        return "%s|out%d|f%s%s" % (node_path, output_index, frame_text, suffix)

    def _snapshot_node_output(
        self,
        node: Any,
        output_index: int = 0,
        frame: Optional[float] = None,
        suffix: str = "",
    ) -> Optional[GeometrySnapshot]:
        if not _is_sop(node):
            return None
        target_frame = self.original_frame if frame is None else float(frame)
        node_path = _node_path(node)
        cache_key = (node_path, int(output_index), round(target_frame, 6))
        cached = self._snapshot_cache.get(cache_key)
        if cached is not None:
            return cached
        key = self._snapshot_key(node_path, output_index, target_frame, suffix)
        if key in self.snapshots:
            return self.snapshots[key]
        try:
            if frame is None or abs(target_frame - self.original_frame) < 1e-6:
                geometry = node.geometry(output_index)
            else:
                geometry = node.geometryAtFrame(target_frame, output_index)
            if geometry is None:
                return None
            snapshot = build_geometry_snapshot(
                geometry,
                key,
                _node_path(node),
                output_index,
                target_frame,
                deep=self.scan_level == "deep",
            )
            self.snapshots[key] = snapshot
            self._snapshot_cache[cache_key] = snapshot
            self._diagnose_geometry_health(snapshot)
            return snapshot
        except Exception as exc:
            self.add_issue(
                "GEOMETRY_SNAPSHOT_FAILED",
                "warning",
                "high",
                "geometry",
                _node_path(node),
                "Geometryを取得できませんでした",
                {"output_index": output_index, "frame": target_frame, "error": "%s: %s" % (exc.__class__.__name__, exc)},
                "ノードのCook状態、入力、ロックされたHDA、時間依存を確認してください。",
            )
            return None

    def _snapshot_input(self, node: Any, input_index: int, frame: Optional[float] = None) -> Optional[GeometrySnapshot]:
        connection = None
        for candidate in _safe(lambda: node.inputConnections(), ()) or ():
            if int(_safe(lambda candidate=candidate: candidate.inputIndex(), -1)) == input_index:
                connection = candidate
                break
        if connection is None:
            return None
        source_node = _safe(lambda: connection.inputNode(), None)
        output_index = int(_safe(lambda: connection.outputIndex(), 0) or 0)
        if source_node is None:
            return None
        return self._snapshot_node_output(source_node, output_index, frame, suffix="|for:%s:in%d" % (_node_path(node), input_index))

    def _collect_main_snapshots(self) -> None:
        candidates = [node for node in self.nodes if self._should_snapshot_node(node)]
        limit = 220 if self.scan_level == "deep" else 80
        if len(candidates) > limit:
            self.scan_notes.append(
                "Geometry snapshot candidates were limited from %d to %d. Use a smaller selection for complete lineage."
                % (len(candidates), limit)
            )
            candidates = candidates[:limit]
        for index, node in enumerate(candidates, 1):
            self._emit_progress("Geometry検査: " + _node_path(node), index, len(candidates))
            self._snapshot_node_output(node, 0)

    def _diagnose_high_signal_internal_messages(self) -> None:
        """Surface only actionable messages hidden inside cooked HDAs.

        Ordinary locked-HDA warnings are extremely noisy.  This deliberately
        ignores them and forwards only messages whose text carries measurable
        failure/performance evidence, such as Scatter's emergency point cap.
        """
        seen: Set[Tuple[str, str]] = set()
        for node in self.nodes:
            if not (_is_rbd_node(node) or _is_apex_node(node) or _is_kinefx_node(node)):
                continue
            node_text = _node_type_text(node)
            if self.scan_level == "standard" and "rbdmaterialfracture" not in node_text:
                continue
            candidate_tokens = ("scatter",) if self.scan_level == "standard" else INTERNAL_MESSAGE_NODE_TOKENS
            descendants = list(_safe(lambda node=node: node.allSubChildren(), ()) or ())
            if len(descendants) > 6000:
                descendants = descendants[:6000]
                self.scan_notes.append("Internal message scan was limited to 6000 nodes for %s." % _node_path(node))
            for child in descendants:
                child_token = (
                    str(_safe(lambda child=child: child.name(), "") or "")
                    + " "
                    + _node_type_text(child)
                ).lower()
                if not any(token in child_token for token in candidate_tokens):
                    continue
                messages = list(_safe(lambda child=child: child.errors(), ()) or ())
                messages.extend(list(_safe(lambda child=child: child.warnings(), ()) or ()))
                for message in messages:
                    text = str(message).strip()
                    if not text or INTERNAL_HIGH_SIGNAL_RE.search(text) is None:
                        continue
                    normalized = re.sub(r"\s+", " ", text)
                    key = (_node_path(node), normalized)
                    if key in seen:
                        continue
                    seen.add(key)
                    child_path = _node_path(child)
                    constraint_connection_scatter = bool(
                        "update_constraints" in child_path.lower()
                        and "connectadjacentpieces" in child_path.lower()
                        and "scatter" in child_path.lower()
                    )
                    self.add_issue(
                        "HOUDINI_INTERNAL_HIGH_SIGNAL_MESSAGE",
                        "warning",
                        "high",
                        "performance" if "scatter" in normalized.lower() or "points" in normalized.lower() else "houdini",
                        _node_path(node),
                        "内部ノードに数値付きの高信号メッセージがあります",
                        {
                            "internal_node": child_path,
                            "message": normalized,
                            "operation_scope": (
                                "constraint_connection_sampling"
                                if constraint_connection_scatter
                                else "internal_operation_not_classified"
                            ),
                            "fracture_site_count_not_established": constraint_connection_scatter,
                            "simulation_behavior_effect_not_established": True,
                        },
                        "Constraint接続用Scatterなら、まずCook時間と生成Constraint被覆を確認してください。Fracture Site数とは別です。"
                        if constraint_connection_scatter
                        else "内部ノードの数値上限・生成数・Cook結果を確認してください。",
                        ["performance", "apex_graph"],
                        [child_path],
                    )

    def _diagnose_geometry_health(self, snapshot: GeometrySnapshot) -> None:
        path = snapshot.node_path
        if snapshot.valid is False:
            self.add_issue(
                "GEOMETRY_INVALID",
                "error",
                "high",
                "geometry",
                path,
                "hou.Geometryが無効状態です",
            )
        if snapshot.counts.get("points", 0) == 0 and snapshot.counts.get("primitives", 0) == 0:
            node = _safe(lambda: hou.node(path), None) if hou is not None else None
            used_output_indices = {
                int(_safe(lambda connection=connection: connection.outputIndex(), -1))
                for connection in (_safe(lambda: node.outputConnections(), ()) or ())
            } if node is not None else set()
            unused_output_with_other_used_output = bool(
                used_output_indices and snapshot.output_index not in used_output_indices
            )
            standalone_control = bool(
                node is not None
                and "null" in _node_type_name(node).lower()
                and not any(item is not None for item in (_safe(lambda: node.inputs(), ()) or ()))
                and not (_safe(lambda: node.outputs(), ()) or ())
            )
            if standalone_control or unused_output_with_other_used_output:
                return
            self.add_issue(
                "GEOMETRY_EMPTY",
                "warning",
                "high",
                "geometry",
                path,
                "Geometryが空です",
                {"output_index": snapshot.output_index, "frame": snapshot.frame},
            )
        diagonal = float(snapshot.bbox.get("diagonal", 0.0) or 0.0)
        if diagonal > 1_000_000 or (0 < diagonal < 1e-7):
            self.add_issue(
                "GEOMETRY_EXTREME_SCALE",
                "warning",
                "high",
                "geometry",
                path,
                "Geometryのワールドスケールが極端です",
                {"bbox_diagonal": diagonal, "bbox": snapshot.bbox},
                "単位、Transform、Import Scale、Bullet World Scaleを確認してください。",
                ["rbd_general", "apex_graph"],
            )
        if snapshot.degenerate_primitives:
            self.add_issue(
                "MESH_DEGENERATE_PRIMITIVES",
                "error",
                "high",
                "mesh",
                path,
                "閉じたSurface Polygonに縮退面が検出されました",
                {
                    "closed_surface_degenerate_count": snapshot.degenerate_primitives,
                    "closed_polygon_count": snapshot.closed_polygon_primitive_count,
                    "open_polyline_count": snapshot.open_polyline_primitive_count,
                    "two_endpoint_open_line_count": snapshot.two_endpoint_open_line_count,
                    "output_index": snapshot.output_index,
                    "primitive_role_sample_complete": snapshot.primitive_role_sampled == snapshot.counts.get("primitives", 0),
                },
                "閉じたSurfaceだけを対象にPolyDoctor、Clean、Fuse許容値、Fracture設定を確認してください。",
                ["rbd_general", "performance"],
            )
        if self.scan_level == "deep" and snapshot.closed_polygon_primitive_count > 0:
            node = _safe(lambda: hou.node(path), None) if hou is not None else None
            node_text = _node_type_text(node) if node is not None else ""
            if any(token in node_text for token in ("rbdmaterialfracture", "rbdunpack")):
                self.add_check(
                    "MESH_CLOSED_SURFACE_HEALTH",
                    "pass" if snapshot.degenerate_primitives == 0 else "review",
                    "mesh",
                    path,
                    {
                        "context": "output_%d_closed_surfaces" % snapshot.output_index,
                        "closed_polygon_count": snapshot.closed_polygon_primitive_count,
                        "closed_surface_degenerate_count": snapshot.degenerate_primitives,
                        "open_polyline_count": snapshot.open_polyline_primitive_count,
                        "primitive_role_sample_complete": snapshot.primitive_role_sampled == snapshot.counts.get("primitives", 0),
                    },
                )
        if snapshot.nonmanifold_edges:
            self.add_issue(
                "MESH_NONMANIFOLD_EDGES",
                "warning",
                "high",
                "mesh",
                path,
                "3面以上が共有する非多様体Edgeが検出されました",
                {"count": snapshot.nonmanifold_edges},
                "Boolean／Fracture後の重複面とFuseを確認してください。",
                ["rbd_general"],
            )
        if snapshot.packed_bad_transforms:
            self.add_issue(
                "PACKED_TRANSFORM_SINGULAR",
                "error",
                "high",
                "geometry",
                path,
                "行列式が0または非有限のPacked Transformがあります",
                {"count": snapshot.packed_bad_transforms},
                "ゼロScale、壊れたTransform、APEX/KineFXの行列計算を確認してください。",
                ["frame_one_explosion", "apex_graph"],
            )
        for stat in snapshot.stats.values():
            if stat.nonfinite_count:
                self.add_issue(
                    "ATTRIBUTE_NONFINITE_VALUES",
                    "error",
                    "high",
                    "attribute",
                    path,
                    "非有限値を持つ属性があります: %s (%s)" % (stat.name, stat.owner),
                    {"attribute": stat.to_dict()},
                    "NaN/Infが最初に発生した上流ノードを属性Lineageで確認してください。",
                    ["frame_one_explosion", "apex_graph"],
                )
        if snapshot.counts.get("primitives", 0) > 2_000_000:
            self.add_issue(
                "GEOMETRY_VERY_HIGH_PRIMITIVE_COUNT",
                "warning",
                "high",
                "performance",
                path,
                "Primitive数が非常に多いです",
                {"primitives": snapshot.counts.get("primitives")},
                "表示GeometryとCollision Proxyを分け、Cache境界を設けてください。",
                ["performance"],
            )

    def _main_snapshot_for_node(self, node: Any) -> Optional[GeometrySnapshot]:
        key = self._snapshot_key(_node_path(node), 0, self.original_frame)
        return self.snapshots.get(key)

    def _diagnose_attribute_lineage(self) -> None:
        selected_paths = {_node_path(node) for node in self.nodes}
        for node in self.nodes:
            downstream = self._main_snapshot_for_node(node)
            if downstream is None:
                continue
            allowed_inputs = self._lineage_input_indices(node)
            for connection in _safe(lambda node=node: node.inputConnections(), ()) or ():
                input_index = int(_safe(lambda connection=connection: connection.inputIndex(), -1))
                if input_index not in allowed_inputs:
                    continue
                source = _safe(lambda connection=connection: connection.inputNode(), None)
                output_index = int(_safe(lambda connection=connection: connection.outputIndex(), 0) or 0)
                if source is None or _node_path(source) not in selected_paths:
                    continue
                upstream = self._snapshot_node_output(
                    source,
                    output_index,
                    suffix="|lineage:%s:in%d" % (_node_path(node), input_index),
                )
                if upstream is None:
                    continue
                self._compare_attribute_snapshots(upstream, downstream, node)

    def _lineage_input_indices(self, node: Any) -> Set[int]:
        connections = list(_safe(lambda: node.inputConnections(), ()) or ())
        connected = {
            int(_safe(lambda connection=connection: connection.inputIndex(), -1))
            for connection in connections
        }
        connected.discard(-1)
        if not connected:
            return set()
        text = _node_type_text(node)
        # Merge output contains additions from every input, so pairwise
        # before/after language is not valid. Its final contract is checked at
        # the RBD/APEX consumer instead.
        if "merge" in text:
            return set()
        if "switch" in text:
            selected = self._parm_value(node, ("input", "selectinput", "switcher"), None)
            if isinstance(selected, (int, float)) and int(selected) in connected:
                return {int(selected)}
            return set()
        # Source input 1 of Attribute Copy is a lookup source, not the object
        # that flows to output 0.
        if "attribcopy" in text or "attribute copy" in text:
            return {0} if 0 in connected else set()
        # Native RBD three-stream nodes map Geometry/Constraint/Proxy by port.
        # Generic output-0 lineage therefore follows only input 0; the other
        # streams are validated by _diagnose_rbd_contract.
        if any(token in text for token in ("rbdmaterialfracture", "rbdcluster", "rbdconfigure", "rbdpack", "rbdunpack", "rbdbulletsolver", "rbdconstraintproperties")):
            return {0} if 0 in connected else set()
        if len(connected) == 1:
            return set(connected)
        # Ambiguous multi-input SOPs are skipped rather than described with an
        # invalid causal before/after comparison.
        return set()

    def _expected_lineage_transition(self, node: Any, attribute: str) -> bool:
        text = _node_type_text(node)
        if attribute == "name" and any(
            token in text
            for token in (
                "fracture", "name", "assemble", "connectivity", "cluster", "pack", "unpack",
                "attribpromote", "attribute promote", "fuse", "clean", "blast", "split", "rbdconfigure",
            )
        ):
            return True
        if attribute == "sourceprim" and any(
            token in text
            for token in (
                "fracture", "cluster", "pack", "unpack", "rbdconfigure", "blast", "split",
                "attribcopy", "attribute copy", "fuse", "clean",
            )
        ):
            return True
        if attribute in ("active", "animated", "deforming") and any(
            token in text for token in ("rbdconfigure", "switch", "attribcopy", "attribute copy")
        ):
            return True
        if attribute in ("constraint_name", "strength") and any(
            token in text for token in ("rbdconstraint", "constraint properties", "blast", "split")
        ):
            return True
        return False

    @staticmethod
    def _stat_packet(stat: AttributeStats) -> Dict[str, Any]:
        packet: Dict[str, Any] = {
            "owner": stat.owner,
            "element_count": stat.count,
            "sampled_count": stat.sampled,
            "sample_is_complete": stat.sampled == stat.count,
            "unique_count": stat.unique_count,
            "empty_count": stat.empty_count,
        }
        if stat.minimum is not None:
            packet["minimum"] = stat.minimum
        if stat.maximum is not None:
            packet["maximum"] = stat.maximum
        if stat.vector_max_length is not None:
            packet["vector_max_length"] = stat.vector_max_length
        packet["negative_count"] = stat.negative_count
        packet["zero_count"] = stat.zero_count
        packet["positive_count"] = stat.positive_count
        return packet

    @staticmethod
    def _identity_set(stat: Optional[AttributeStats]) -> Optional[Set[str]]:
        if stat is None or stat.sampled != stat.count:
            return None
        return {str(value) for value in stat.values if str(value)}

    def _identity_transfer_is_explicit(
        self,
        name: str,
        upstream: GeometrySnapshot,
        downstream: GeometrySnapshot,
    ) -> bool:
        if name != "name":
            return False
        before = upstream.any_stat("name")
        after = downstream.any_stat("source_piece_name")
        before_set = self._identity_set(before)
        after_set = self._identity_set(after)
        return before_set is not None and after_set is not None and before_set == after_set

    def _compare_attribute_snapshots(
        self,
        upstream: GeometrySnapshot,
        downstream: GeometrySnapshot,
        downstream_node: Any,
    ) -> None:
        path = _node_path(downstream_node)
        upstream_owner = {name: upstream.attribute_owner(name) for name in PROTECTED_ATTRIBUTES}
        downstream_owner = {name: downstream.attribute_owner(name) for name in PROTECTED_ATTRIBUTES}
        for name in sorted(PROTECTED_ATTRIBUTES):
            up_owner = upstream_owner.get(name)
            down_owner = downstream_owner.get(name)
            expected = self._expected_lineage_transition(downstream_node, name)
            if up_owner and not down_owner and not expected and not self._identity_transfer_is_explicit(name, upstream, downstream):
                self.add_issue(
                    "PROTECTED_ATTRIBUTE_REMOVED",
                    "warning",
                    "medium",
                    "attribute",
                    path,
                    "保護属性の出力存在を要確認: " + name,
                    {
                        "attribute": name,
                        "upstream": upstream.node_path,
                        "input_owner": up_owner,
                        "output_owner": None,
                        "compared_stream": "input0_to_output0",
                        "downstream_reference_to_attribute_not_measured": True,
                        "causal_effect_not_established": True,
                    },
                    "この属性を下流が使用する場合のみ、ノードの意図と別出力への移動を確認してください。",
                    ["frame_one_explosion", "cache", "apex_graph"],
                    [upstream.node_path],
                )
            if up_owner and down_owner and up_owner != down_owner and not expected:
                self.add_issue(
                    "ATTRIBUTE_OWNER_CHANGED",
                    "notice",
                    "medium",
                    "attribute",
                    path,
                    "属性Classの入出力差を要確認: " + name,
                    {"upstream": upstream.node_path, "input_owner": up_owner, "output_owner": down_owner},
                    "Class差そのものは異常を確定しません。下流が要求するClassと照合してください。",
                    ["frame_one_explosion", "apex_graph"],
                    [upstream.node_path],
                )

        for name in ("name", "friction", "active", "animated", "v", "w", "sourceprim", "cluster"):
            up_stat = upstream.any_stat(name)
            down_stat = downstream.any_stat(name)
            if up_stat is None or down_stat is None or up_stat.fingerprint == down_stat.fingerprint:
                continue
            if self._expected_lineage_transition(downstream_node, name):
                continue
            if name == "name":
                before_set = self._identity_set(up_stat)
                after_set = self._identity_set(down_stat)
                if before_set is None or after_set is None or before_set == after_set:
                    continue
                only_before = sorted(before_set - after_set)
                only_after = sorted(after_set - before_set)
                self.add_issue(
                    "IDENTITY_SET_DIFFERENCE",
                    "warning",
                    "high",
                    "attribute",
                    path,
                    "name集合に入出力差があります",
                    {
                        "upstream": upstream.node_path,
                        "input_unique_count": len(before_set),
                        "output_unique_count": len(after_set),
                        "input_only_count": len(only_before),
                        "input_only_sample": only_before[:12],
                        "output_only_count": len(only_after),
                        "output_only_sample": only_after[:12],
                        "sets_measured_exactly": True,
                    },
                    "フィルタ・再命名・追加ピースのどれに該当するかをノード用途から判断してください。",
                    ["frame_one_explosion", "cache"],
                    [upstream.node_path],
                )
                continue
            before_names = self._identity_set(upstream.any_stat("name"))
            after_names = self._identity_set(downstream.any_stat("name"))
            identity_stable = before_names is not None and after_names is not None and before_names == after_names
            if not identity_stable and up_stat.count != down_stat.count:
                continue
            self.add_issue(
                "ATTRIBUTE_DISTRIBUTION_DIFFERENCE",
                "notice",
                "medium",
                "attribute",
                path,
                "属性分布に入出力差があります: " + name,
                {
                    "upstream": upstream.node_path,
                    "identity_set_equal": identity_stable,
                    "input": self._stat_packet(up_stat),
                    "output": self._stat_packet(down_stat),
                },
                "この差だけでは異常を確定しません。ノードの設定目的とSolver最終入力を照合してください。",
                ["sliding", "frame_one_explosion", "cache"],
                [upstream.node_path],
            )

    def _diagnose_identity_empty_transitions(self) -> None:
        for node in self.nodes:
            downstream = self._main_snapshot_for_node(node)
            if downstream is None:
                continue
            empty_stats = [
                stat
                for stat in downstream.stats.values()
                if stat.name in IDENTITY_ATTRIBUTES
                and "string" in stat.data_type.lower()
                and stat.sampled > 0
                and stat.sampled == stat.count
                and stat.empty_count == stat.sampled
            ]
            if not empty_stats:
                continue
            allowed_inputs = self._lineage_input_indices(node)
            if not allowed_inputs:
                continue
            for connection in _safe(lambda node=node: node.inputConnections(), ()) or ():
                input_index = int(_safe(lambda connection=connection: connection.inputIndex(), -1))
                if input_index not in allowed_inputs:
                    continue
                source = _safe(lambda connection=connection: connection.inputNode(), None)
                if source is None:
                    continue
                output_index = int(_safe(lambda connection=connection: connection.outputIndex(), 0) or 0)
                upstream = self._snapshot_node_output(
                    source,
                    output_index,
                    suffix="|empty-transition:%s:in%d" % (_node_path(node), input_index),
                )
                if upstream is None:
                    continue
                for down_stat in empty_stats:
                    up_stat = upstream.any_stat(down_stat.name)
                    if up_stat is None or up_stat.sampled != up_stat.count:
                        continue
                    input_nonempty_count = up_stat.sampled - up_stat.empty_count
                    if input_nonempty_count <= 0:
                        continue
                    canonical_identity = down_stat.name == "name"
                    canonical_name_stat = downstream.any_stat("name")
                    canonical_name_nonempty_count = None
                    if canonical_name_stat is not None:
                        canonical_name_nonempty_count = canonical_name_stat.sampled - canonical_name_stat.empty_count
                    self.add_issue(
                        "IDENTITY_ATTRIBUTE_ALL_EMPTY_TRANSITION" if canonical_identity else "AUXILIARY_IDENTITY_ALL_EMPTY_TRANSITION",
                        "warning" if canonical_identity else "info",
                        "high" if canonical_identity else "medium",
                        "attribute",
                        _node_path(node),
                        ("Canonical identity属性" if canonical_identity else "補助identity属性")
                        + "が全空値になる境界を測定: " + down_stat.name,
                        {
                            "attribute": down_stat.name,
                            "canonical_rbd_identity_attribute": canonical_identity,
                            "canonical_name_nonempty_count_at_output": canonical_name_nonempty_count,
                            "downstream_reference_to_this_attribute_not_measured": True,
                            "causal_effect_not_established": True,
                            "input_node": upstream.node_path,
                            "input_owner": up_stat.owner,
                            "input_element_count": up_stat.count,
                            "input_empty_value_count": up_stat.empty_count,
                            "input_nonempty_value_count": input_nonempty_count,
                            "output_owner": down_stat.owner,
                            "output_element_count": down_stat.count,
                            "output_empty_value_count": down_stat.empty_count,
                            "output_nonempty_value_count": 0,
                            "values_measured_exactly": True,
                        },
                        "この属性を下流が使用する場合のみ、当該ノードの属性転送設定を確認してください。",
                        ["cache", "glue", "apex_graph"] if canonical_identity else ["cache", "apex_graph"],
                        [upstream.node_path],
                    )

    def _diagnose_group_parameters(self) -> None:
        for node in self.nodes:
            if not _is_sop(node):
                continue
            group_parms = []
            for parm in _safe(lambda node=node: node.parms(), ()) or ():
                name = str(_safe(lambda parm=parm: parm.name(), "") or "")
                template = _safe(lambda parm=parm: parm.parmTemplate(), None)
                if template is None:
                    continue
                template_type = _safe(lambda template=template: template.type(), None)
                string_type = getattr(getattr(hou, "parmTemplateType", None), "String", None) if hou is not None else None
                is_string = bool(
                    (string_type is not None and template_type == string_type)
                    or (hou is not None and isinstance(template, getattr(hou, "StringParmTemplate", tuple())))
                )
                if not is_string:
                    continue
                label = str(_safe(lambda template=template: template.label(), "") or "")
                token = (name + " " + label).lower().replace(" ", "")
                if not any(item in token for item in GROUP_PARM_TOKENS):
                    continue
                if any(item in token for item in ("grouptype", "groupname", "creategroup", "dogroup", "newgroup", "groupconnected")):
                    continue
                group_parms.append((parm, name))
            if not group_parms:
                continue
            input_snapshot = self._snapshot_input(node, 0)
            if input_snapshot is None:
                continue
            geometry = _safe(lambda node=node: node.inputGeometry(0), None)
            if geometry is None:
                continue
            for parm, name in group_parms:
                value = _safe(lambda parm=parm: parm.evalAsString(), "")
                if not isinstance(value, str) or not value.strip() or len(value) > 2000:
                    continue
                pattern = value.strip()
                point_matches: Optional[int] = None
                prim_matches: Optional[int] = None
                point_error = ""
                prim_error = ""
                try:
                    point_matches = len(geometry.globPoints(pattern))
                except Exception as exc:
                    point_error = str(exc)
                try:
                    prim_matches = len(geometry.globPrims(pattern))
                except Exception as exc:
                    prim_error = str(exc)

                referenced_attrs = sorted(set(ATTRIBUTE_REF_RE.findall(pattern)))
                missing_attrs = []
                available = {
                    attr_name
                    for attrs in input_snapshot.attributes.values()
                    for attr_name in attrs
                }
                for attr_name in referenced_attrs:
                    if attr_name not in available:
                        missing_attrs.append(attr_name)
                if missing_attrs:
                    self.add_issue(
                        "GROUP_PATTERN_ATTRIBUTE_MISSING",
                        "error",
                        "high",
                        "group",
                        _node_path(node),
                        "Group式が存在しない属性を参照しています",
                        {
                            "parameter": name,
                            "pattern": pattern,
                            "missing_attributes": missing_attrs,
                            "input_node": input_snapshot.node_path,
                        },
                        "属性の綴り、Class、Attribute Delete位置を確認してください。",
                        ["glue", "apex_graph"],
                    )
                if point_matches == 0 and prim_matches == 0:
                    self.add_issue(
                        "GROUP_PATTERN_EMPTY",
                        "warning",
                        "medium",
                        "group",
                        _node_path(node),
                        "Group式の一致数が0です",
                        {
                            "parameter": name,
                            "point_matches": point_matches,
                            "primitive_matches": prim_matches,
                            "point_error": point_error,
                            "primitive_error": prim_error,
                        },
                        "0件が意図した除外条件か、Group名・Class・入力Branchの不一致かを確認してください。",
                        ["glue", "apex_graph"],
                    )
                point_total = input_snapshot.counts.get("points", 0)
                prim_total = input_snapshot.counts.get("primitives", 0)
                if point_matches == point_total and point_total > 0 and prim_matches in (None, 0):
                    self.add_issue(
                        "GROUP_PATTERN_SELECTS_ALL_POINTS",
                        "notice",
                        "medium",
                        "group",
                        _node_path(node),
                        "Group指定が全ポイントを選択しています",
                        {"parameter": name, "pattern": pattern, "count": point_total},
                        "部分処理を意図している場合はGroup式を見直してください。",
                    )
                if prim_matches == prim_total and prim_total > 0 and point_matches in (None, 0):
                    self.add_issue(
                        "GROUP_PATTERN_SELECTS_ALL_PRIMITIVES",
                        "notice",
                        "medium",
                        "group",
                        _node_path(node),
                        "Group指定が全Primitiveを選択しています",
                        {"parameter": name, "pattern": pattern, "count": prim_total},
                        "Constraint全体の一斉変更になっていないか確認してください。",
                        ["glue"],
                    )

    def _parm(self, node: Any, *names: str) -> Any:
        for name in names:
            parm = _safe(lambda name=name: node.parm(name), None)
            if parm is not None:
                return parm
        return None

    def _parm_value(self, node: Any, names: Sequence[str], default: Any = None) -> Any:
        parm = self._parm(node, *names)
        if parm is None:
            return default
        return _safe(lambda: parm.eval(), default)

    def _parm_string(self, node: Any, names: Sequence[str], default: str = "") -> str:
        parm = self._parm(node, *names)
        if parm is None:
            return default
        return str(_safe(lambda: parm.evalAsString(), default) or default)

    def _profile_enabled(self, profile: str) -> bool:
        return self.profile in ("auto", profile)

    def _upstream_time_dependent_paths(self, node: Any, max_depth: int = 24) -> List[str]:
        if node is None:
            return []
        found: List[str] = []
        visited: Set[str] = set()
        frontier = [node]
        depth = 0
        while frontier and depth <= max_depth and len(visited) < 1000:
            next_frontier = []
            for current in frontier:
                current_path = _node_path(current)
                if not current_path or current_path in visited:
                    continue
                visited.add(current_path)
                if current_path in self.time_dependent_nodes:
                    found.append(current_path)
                next_frontier.extend(
                    item for item in (_safe(lambda current=current: current.inputs(), ()) or ()) if item is not None
                )
            frontier = next_frontier
            depth += 1
        return sorted(set(found))

    def _diagnose_rbd_profiles(self) -> None:
        if not self._profile_enabled("rbd"):
            return
        for node in self.nodes:
            text = _node_type_text(node)
            if "rbdbulletsolver" in text or ("rbd bullet solver" in text):
                self._diagnose_rbd_solver(node)
            elif self.scan_level != "fast" and "rbdconfigure" in text:
                self._diagnose_rbd_configure_active_bounds(node)
            elif self.scan_level != "fast" and "rbdmaterialfracture" in text:
                geometry = self._snapshot_node_output(node, 0)
                constraints = self._snapshot_node_output(node, 1)
                proxy = self._snapshot_node_output(node, 2)
                self._diagnose_rbd_contract(_node_path(node), geometry, constraints, proxy, "RBD Material Fracture outputs")
            elif self.scan_level != "fast" and "rbdunpack" in text:
                geometry = self._snapshot_node_output(node, 0)
                constraints = self._snapshot_node_output(node, 1)
                proxy = self._snapshot_node_output(node, 2)
                self._diagnose_rbd_contract(_node_path(node), geometry, constraints, proxy, "RBD Unpack outputs")
            elif self.scan_level != "fast" and "rbdpack" in text:
                geometry = self._snapshot_input(node, 0)
                constraints = self._snapshot_input(node, 1)
                proxy = self._snapshot_input(node, 2)
                self._diagnose_rbd_contract(_node_path(node), geometry, constraints, proxy, "RBD Pack inputs")

    def _diagnose_rbd_configure_active_bounds(self, node: Any) -> None:
        """Measure how an RBD Configure Active/Use Bounds setup covers pieces."""
        if not bool(self._parm_value(node, ("addactive1",), 0)):
            return
        if not bool(self._parm_value(node, ("useactivebounds1",), 0)):
            return
        configured_active = self._parm_value(node, ("active1",), None)
        proxy = self._snapshot_node_output(node, 2)
        if proxy is None:
            return
        active = proxy.stat("point", "active")
        animated = proxy.stat("point", "animated")
        if active is None or active.sampled <= 0:
            return
        piece_count = active.sampled
        active_count = active.positive_count
        animated_count = animated.positive_count if animated is not None else None
        active_ratio = active_count / float(piece_count)
        bounds_size = [
            self._parm_value(node, ("bboxsizex",), None),
            self._parm_value(node, ("bboxsizey",), None),
            self._parm_value(node, ("bboxsizez",), None),
        ]
        bounds_center = [
            self._parm_value(node, ("bboxcenterx",), None),
            self._parm_value(node, ("bboxcentery",), None),
            self._parm_value(node, ("bboxcenterz",), None),
        ]
        evidence = {
            "context": "rbd_configure_active_use_bounds_output_proxy",
            "output_index": 2,
            "piece_count": piece_count,
            "active_positive_count": active_count,
            "active_ratio": active_ratio,
            "animated_positive_count": animated_count,
            "configured_active_value": configured_active,
            "bounds_size": bounds_size,
            "bounds_center": bounds_center,
            "output_bbox_size": proxy.bbox.get("size"),
            "values_measured_exactly": active.sampled == active.count,
            "downstream_override_not_excluded": True,
        }
        self.add_check(
            "RBD_CONFIGURE_ACTIVE_BOUNDS_COVERAGE",
            "review",
            "rbd",
            _node_path(node),
            evidence,
            "Coverage measurement only; verify whether selected bounds represent the movable interior or the fixed frame.",
        )
        sparse_limit = max(3, int(piece_count * 0.01))
        if configured_active is not None and float(configured_active) > 0 and active_count <= sparse_limit:
            self.add_issue(
                "RBD_CONFIGURE_ACTIVE_BOUNDS_SPARSE_COVERAGE",
                "warning",
                "high",
                "rbd",
                _node_path(node),
                "RBD ConfigureのActive Boundsが動的Pieceをほとんど選択していません",
                evidence,
                "Sourceをスケール変更した場合は、Use BoundsのCenter/Sizeも現在のPacked Piece範囲に合わせてください。",
                ["no_motion", "rbd_general"],
            )

    def _diagnose_rbd_solver(self, solver: Any) -> None:
        path = _node_path(solver)
        inputs = list(_safe(lambda: solver.inputs(), ()) or ())
        connected = [index for index, item in enumerate(inputs) if item is not None]
        if not connected or 0 not in connected:
            self.add_issue(
                "RBD_SOLVER_GEOMETRY_INPUT_MISSING",
                "critical",
                "high",
                "rbd",
                path,
                "RBD Bullet SolverのGeometry入力がありません",
                symptoms=["rbd_general"],
            )
            return
        if 2 not in connected:
            self.add_issue(
                "RBD_SOLVER_PROXY_INPUT_MISSING",
                "warning",
                "high",
                "rbd",
                path,
                "RBD Bullet SolverのProxy入力がありません",
                suggestion="表示Geometryを直接Collisionに使う意図でなければProxy Branchを接続してください。",
                symptoms=["performance", "tunneling"],
            )
        if 1 not in connected:
            self.add_issue(
                "RBD_SOLVER_CONSTRAINT_INPUT_MISSING",
                "notice",
                "high",
                "rbd",
                path,
                "RBD Bullet SolverへConstraint Geometryが接続されていません",
                suggestion="Glueを使用しない構成なら問題ありません。",
                symptoms=["glue"],
            )

        if self.scan_level != "fast":
            geometry = self._snapshot_input(solver, 0)
            constraints = self._snapshot_input(solver, 1)
            proxy = self._snapshot_input(solver, 2)
            collider = self._snapshot_input(solver, 3)
            self._diagnose_rbd_contract(path, geometry, constraints, proxy, "RBD Bullet Solver inputs")
            if geometry is not None:
                self._diagnose_rbd_piece_attributes(path, geometry, solver)
            if constraints is not None:
                self._diagnose_constraint_geometry(path, constraints, geometry)
                self._diagnose_rbd_impact_topology(path, constraints, geometry, solver)
            if collider is not None:
                self._diagnose_external_collider(path, collider, solver)
            start_geometry = self._snapshot_input(solver, 0, frame=self.start_frame)
            if start_geometry is not None:
                self._diagnose_initial_rbd_state(path, start_geometry)

        substeps = self._parm_value(solver, ("substep", "substeps", "minsubsteps"), None)
        iterations = self._parm_value(solver, ("numiteration", "constraintiterations", "iterations"), None)
        if isinstance(substeps, (int, float)) and substeps < 2 and len(inputs) > 3 and inputs[3] is not None:
            self.add_issue(
                "RBD_FAST_COLLIDER_LOW_SUBSTEPS",
                "warning",
                "medium",
                "rbd",
                path,
                "外部コライダーに対してSubstepsが低い可能性があります",
                {"substeps": substeps},
                "高速衝突でのみすり抜ける場合はSubstepsとCollider vを確認してください。",
                ["tunneling"],
            )
        if isinstance(substeps, (int, float)) and isinstance(iterations, (int, float)) and substeps * iterations > 1000:
            self.add_issue(
                "RBD_SOLVER_EXPENSIVE_SETTINGS",
                "warning",
                "high",
                "performance",
                path,
                "Substeps × Constraint Iterationsが非常に大きいです",
                {"substeps": substeps, "iterations": iterations, "product": substeps * iterations},
                "Proxy、Margin、Constraint構造を直したうえで必要最小限に下げてください。",
                ["performance"],
            )

        ground_friction = self._parm_value(solver, ("ground_friction",), None)
        ground_bounce = self._parm_value(solver, ("ground_bounce",), None)
        if isinstance(ground_friction, (int, float)) and ground_friction < 0.05:
            self.add_issue(
                "RBD_GROUND_FRICTION_VERY_LOW",
                "warning",
                "high",
                "rbd",
                path,
                "Ground Frictionが非常に低いです",
                {"ground_friction": ground_friction},
                "破片が床で滑り続ける場合はGroundとPiece双方のfrictionを確認してください。",
                ["sliding"],
            )
        if isinstance(ground_bounce, (int, float)) and ground_bounce > 0.8:
            self.add_issue(
                "RBD_GROUND_BOUNCE_HIGH",
                "warning",
                "high",
                "rbd",
                path,
                "Ground Bounceが高いです",
                {"ground_bounce": ground_bounce},
                symptoms=["bouncing"],
            )

        update_enabled = self._parm_value(solver, ("enable_constraintupdates",), 0)
        update_attrs = self._parm_string(solver, ("constraint_attributes",), "")
        if update_enabled and "strength" not in update_attrs.split():
            self.add_issue(
                "RBD_CONSTRAINT_UPDATE_MISSING_STRENGTH",
                "warning",
                "high",
                "rbd",
                path,
                "Constraint Updatesは有効ですがstrengthが更新属性にありません",
                {"constraint_attributes": update_attrs},
                "時間変化するGlue強度を使うならstrengthを追加してください。",
                ["glue"],
            )
        self._diagnose_breaking_thresholds(solver)
        if self.scan_level == "deep" and self.compare_frames:
            self._diagnose_rbd_sim_response_samples(solver)

    def _name_stat(self, snapshot: Optional[GeometrySnapshot]) -> Optional[AttributeStats]:
        if snapshot is None:
            return None
        point_name = snapshot.stat("point", "name")
        primitive_name = snapshot.stat("primitive", "name")
        # Packed RBDs usually have one point per piece.  Unpacked fracture
        # geometry normally repeats primitive name across every polygon of a
        # piece, so primitive name is the authoritative identifier there.
        if snapshot.packed_primitive_count > 0:
            return point_name or primitive_name
        return primitive_name or point_name

    def _name_duplicates_are_invalid(self, snapshot: GeometrySnapshot, stat: AttributeStats) -> bool:
        if not stat.duplicate_count:
            return False
        if snapshot.packed_primitive_count <= 0:
            return False
        # For packed geometry, one packed primitive/point should represent one
        # piece name. Repeated polygon names are expected only when unpacked.
        return True

    def _diagnose_rbd_contract(
        self,
        owner_path: str,
        geometry: Optional[GeometrySnapshot],
        constraints: Optional[GeometrySnapshot],
        proxy: Optional[GeometrySnapshot],
        context: str,
    ) -> None:
        if geometry is None:
            self.add_check(
                "RBD_GEOMETRY_NAME_CONTRACT",
                "not_checked",
                "rbd",
                owner_path,
                {"context": context, "reason": "geometry_snapshot_unavailable"},
            )
            return
        geo_names = self._name_stat(geometry)
        if geo_names is None:
            self.add_check(
                "RBD_GEOMETRY_NAME_CONTRACT",
                "fail",
                "rbd",
                owner_path,
                {"context": context, "name_attribute_present": False, "geometry_source": geometry.node_path},
            )
            self.add_issue(
                "RBD_GEOMETRY_NAME_MISSING",
                "critical",
                "high",
                "rbd",
                owner_path,
                "RBD Geometryにname属性がありません",
                {"context": context, "geometry_source": geometry.node_path},
                "最終破片ごとに一意なPoint nameを作成してください。",
                ["frame_one_explosion", "glue"],
                [geometry.node_path],
            )
            return
        if geo_names.empty_count:
            self.add_issue(
                "RBD_GEOMETRY_EMPTY_NAMES",
                "critical",
                "high",
                "rbd",
                owner_path,
                "空のRBD nameがあります",
                {"count": geo_names.empty_count, "source": geometry.node_path},
                "Name SOPまたはFractureの命名設定を確認してください。",
                ["frame_one_explosion"],
            )
        if self._name_duplicates_are_invalid(geometry, geo_names):
            self.add_issue(
                "RBD_GEOMETRY_DUPLICATE_NAMES",
                "critical",
                "high",
                "rbd",
                owner_path,
                "RBD Geometryに重複nameがあります",
                {"duplicate_count": geo_names.duplicate_count, "unique_count": geo_names.unique_count},
                "二次Fracture後のname再生成とMerge前後を確認してください。",
                ["frame_one_explosion"],
            )
        geometry_name_ok = not geo_names.empty_count and not self._name_duplicates_are_invalid(geometry, geo_names)
        self.add_check(
            "RBD_GEOMETRY_NAME_CONTRACT",
            "pass" if geometry_name_ok else "fail",
            "rbd",
            owner_path,
            {
                "context": context,
                "name_attribute_present": True,
                "owner": geo_names.owner,
                "element_count": geo_names.count,
                "unique_name_count": geo_names.unique_count,
                "empty_name_count": geo_names.empty_count,
                "duplicate_name_count": geo_names.duplicate_count,
                "duplicate_names_invalid_for_representation": self._name_duplicates_are_invalid(geometry, geo_names),
                "representation": "packed" if geometry.packed_primitive_count > 0 else "unpacked",
                "geometry_source": geometry.node_path,
            },
        )

        if proxy is not None:
            if proxy.counts.get("points", 0) == 0 and proxy.counts.get("primitives", 0) == 0:
                self.add_issue(
                    "RBD_PROXY_EMPTY",
                    "critical",
                    "high",
                    "rbd",
                    owner_path,
                    "Proxy Geometryが空です",
                    {"proxy_source": proxy.node_path},
                    symptoms=["tunneling", "collision_offset"],
                )
            proxy_names = self._name_stat(proxy)
            if proxy_names is None:
                self.add_check(
                    "RBD_GEOMETRY_PROXY_NAME_SET",
                    "fail",
                    "rbd",
                    owner_path,
                    {
                        "context": context,
                        "geometry_name_count": geo_names.unique_count,
                        "proxy_name_attribute_present": False,
                        "proxy_source": proxy.node_path,
                    },
                )
                self.add_issue(
                    "RBD_PROXY_NAME_MISSING",
                    "critical",
                    "high",
                    "rbd",
                    owner_path,
                    "Proxy Geometryにname属性がありません",
                    {"proxy_source": proxy.node_path},
                    "Geometryと同じ最終nameをProxyへコピーしてください。",
                    ["frame_one_explosion", "collision_offset"],
                )
            else:
                geo_set = set(str(value) for value in geo_names.values if str(value))
                proxy_set = set(str(value) for value in proxy_names.values if str(value))
                missing = sorted(geo_set - proxy_set)
                extra = sorted(proxy_set - geo_set)
                proxy_duplicate_invalid = self._name_duplicates_are_invalid(proxy, proxy_names)
                self.add_check(
                    "RBD_GEOMETRY_PROXY_NAME_SET",
                    "pass" if not missing and not extra and not proxy_names.empty_count and not proxy_duplicate_invalid else "fail",
                    "rbd",
                    owner_path,
                    {
                        "context": context,
                        "geometry_unique_name_count": len(geo_set),
                        "proxy_unique_name_count": len(proxy_set),
                        "geometry_only_count": len(missing),
                        "proxy_only_count": len(extra),
                        "proxy_empty_name_count": proxy_names.empty_count,
                        "proxy_duplicate_names_invalid": proxy_duplicate_invalid,
                        "sets_measured_exactly": geo_names.sampled == geo_names.count and proxy_names.sampled == proxy_names.count,
                        "geometry_source": geometry.node_path,
                        "proxy_source": proxy.node_path,
                    },
                )
                if missing or extra:
                    self.add_issue(
                        "RBD_GEOMETRY_PROXY_NAME_MISMATCH",
                        "critical",
                        "high",
                        "rbd",
                        owner_path,
                        "GeometryとProxyのname集合が一致しません",
                        {
                            "geometry_unique": len(geo_set),
                            "proxy_unique": len(proxy_set),
                            "missing_from_proxy_count": len(missing),
                            "missing_from_proxy_sample": missing[:20],
                            "extra_in_proxy_count": len(extra),
                            "extra_in_proxy_sample": extra[:20],
                            "geometry_source": geometry.node_path,
                            "proxy_source": proxy.node_path,
                        },
                        "GeometryからCanonical Proxyを再構築するか、nameを同一Branchから渡してください。",
                        ["frame_one_explosion", "collision_offset"],
                        [geometry.node_path, proxy.node_path],
                    )
                if self._name_duplicates_are_invalid(proxy, proxy_names):
                    self.add_issue(
                        "RBD_PROXY_DUPLICATE_NAMES",
                        "critical",
                        "high",
                        "rbd",
                        owner_path,
                        "Proxy Geometryに重複nameがあります",
                        {"duplicate_count": proxy_names.duplicate_count},
                        symptoms=["frame_one_explosion"],
                    )

            geo_center = geometry.bbox.get("center") or []
            proxy_center = proxy.bbox.get("center") or []
            geo_diag = float(geometry.bbox.get("diagonal", 0.0) or 0.0)
            proxy_diag = float(proxy.bbox.get("diagonal", 0.0) or 0.0)
            if len(geo_center) == 3 and len(proxy_center) == 3 and geo_diag > 0:
                center_distance = math.sqrt(
                    sum((float(left) - float(right)) ** 2 for left, right in zip(geo_center, proxy_center))
                )
                ratio = proxy_diag / geo_diag if geo_diag else 0.0
                if center_distance > max(1e-6, geo_diag * 0.05) or ratio < 0.5 or ratio > 2.0:
                    self.add_issue(
                        "RBD_PROXY_BOUNDS_MISMATCH",
                        "warning",
                        "high",
                        "rbd",
                        owner_path,
                        "GeometryとProxyの全体Boundsが大きく異なります",
                        {
                            "geometry_bbox": geometry.bbox,
                            "proxy_bbox": proxy.bbox,
                            "center_distance": center_distance,
                            "diagonal_ratio": ratio,
                        },
                        "Proxy Transform、Scale、name対応、Canonical Proxy生成位置を確認してください。",
                        ["collision_offset", "frame_one_explosion"],
                    )
            geo_prims = geometry.counts.get("primitives", 0)
            proxy_prims = proxy.counts.get("primitives", 0)
            if proxy_prims > 250_000 and proxy_prims > geo_prims * 0.8:
                self.add_issue(
                    "RBD_PROXY_TOO_COMPLEX",
                    "warning",
                    "high",
                    "performance",
                    owner_path,
                    "Collision Proxyが高解像度です",
                    {"geometry_primitives": geo_prims, "proxy_primitives": proxy_prims},
                    "表示Geometryとは別に低解像度Proxyを作成してください。",
                    ["performance"],
                )
        else:
            self.add_check(
                "RBD_GEOMETRY_PROXY_NAME_SET",
                "not_checked",
                "rbd",
                owner_path,
                {"context": context, "reason": "proxy_snapshot_unavailable"},
            )

        if constraints is not None:
            endpoint_names = constraints.stat("point", "name")
            if endpoint_names is None:
                self.add_check(
                    "RBD_CONSTRAINT_ENDPOINT_NAME_SET",
                    "fail",
                    "rbd",
                    owner_path,
                    {"context": context, "endpoint_name_attribute_present": False, "constraint_source": constraints.node_path},
                )
                self.add_issue(
                    "RBD_CONSTRAINT_ENDPOINT_NAME_MISSING",
                    "critical",
                    "high",
                    "rbd",
                    owner_path,
                    "Constraint端点にPoint nameがありません",
                    {"constraint_source": constraints.node_path},
                    "Constraint Geometryの両端Pointへ接続先ピースnameを設定してください。",
                    ["glue", "frame_one_explosion"],
                )
            else:
                geo_set = set(str(value) for value in geo_names.values if str(value))
                endpoint_set = set(str(value) for value in endpoint_names.values if str(value))
                orphan = sorted(endpoint_set - geo_set)
                self.add_check(
                    "RBD_CONSTRAINT_ENDPOINT_NAME_SET",
                    "pass" if not orphan and not endpoint_names.empty_count else "fail",
                    "rbd",
                    owner_path,
                    {
                        "context": context,
                        "geometry_unique_name_count": len(geo_set),
                        "constraint_endpoint_unique_name_count": len(endpoint_set),
                        "orphan_endpoint_name_count": len(orphan),
                        "empty_endpoint_name_count": endpoint_names.empty_count,
                        "sets_measured_exactly": geo_names.sampled == geo_names.count and endpoint_names.sampled == endpoint_names.count,
                        "constraint_source": constraints.node_path,
                    },
                )
                if orphan:
                    self.add_issue(
                        "RBD_CONSTRAINT_ORPHAN_ENDPOINTS",
                        "critical",
                        "high",
                        "rbd",
                        owner_path,
                        "存在しないRBD nameを参照するConstraint端点があります",
                        {"count": len(orphan), "sample": orphan[:30], "constraint_source": constraints.node_path},
                        "Cache、Fracture、Name再生成後にConstraint端点を再同期してください。",
                        ["glue", "frame_one_explosion"],
                    )
        else:
            self.add_check(
                "RBD_CONSTRAINT_ENDPOINT_NAME_SET",
                "not_checked",
                "rbd",
                owner_path,
                {"context": context, "reason": "constraint_snapshot_unavailable"},
            )

    def _constraint_geo_object(self, snapshot: GeometrySnapshot) -> Optional[Any]:
        if hou is None:
            return None
        node = _safe(lambda: hou.node(snapshot.node_path), None)
        if node is None:
            return None
        return _safe(lambda: node.geometry(snapshot.output_index), None)

    def _numeric_primitive_summary(self, geometry: Any, prims: Sequence[Any], name: str) -> Dict[str, Any]:
        attrib = _safe(lambda: geometry.findPrimAttrib(name), None)
        if attrib is None:
            return {"present": False, "count": len(prims)}
        values: List[float] = []
        for prim in prims:
            value = _safe(lambda prim=prim: prim.attribValue(attrib), None)
            if isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value)):
                values.append(float(value))
        values.sort()
        if not values:
            return {"present": True, "count": len(prims), "numeric_count": 0}

        def percentile(fraction: float) -> float:
            return values[int((len(values) - 1) * fraction)]

        unique_values = sorted(set(values))
        result = {
            "present": True,
            "count": len(prims),
            "numeric_count": len(values),
            "minimum": values[0],
            "p10": percentile(0.10),
            "median": percentile(0.50),
            "p90": percentile(0.90),
            "maximum": values[-1],
            "negative_count": sum(value < 0 for value in values),
            "zero_count": sum(value == 0 for value in values),
            "positive_count": sum(value > 0 for value in values),
            "unique_value_sample": unique_values[:12],
            "unique_value_count": len(unique_values),
        }
        if name == "strength":
            finite_breakable = [value for value in values if value >= 0]
            result.update(
                {
                    "negative_value_role": "unbreakable_sentinel",
                    "negative_values_excluded_from_finite_strength_range": True,
                    "finite_strength_count": len(finite_breakable),
                    "finite_strength_minimum": min(finite_breakable) if finite_breakable else None,
                    "finite_strength_median": finite_breakable[len(finite_breakable) // 2] if finite_breakable else None,
                    "finite_strength_maximum": max(finite_breakable) if finite_breakable else None,
                    "minimum_to_maximum_is_not_a_strength_spread_when_negative_values_exist": any(value < 0 for value in values),
                }
            )
        return result

    def _constraint_graph_summary(self, geometry: Any, prims: Sequence[Any]) -> Dict[str, Any]:
        name_attrib = _safe(lambda: geometry.findPointAttrib("name"), None)
        if name_attrib is None:
            return {"measured": False, "reason": "point_name_missing", "primitive_count": len(prims)}
        adjacency: Dict[str, Set[str]] = {}
        line_count = 0
        self_link_count = 0
        for prim in prims:
            points = list(_safe(lambda prim=prim: prim.points(), ()) or ())
            if len(points) != 2:
                continue
            left = str(_safe(lambda: points[0].attribValue(name_attrib), "") or "")
            right = str(_safe(lambda: points[1].attribValue(name_attrib), "") or "")
            if not left or not right:
                continue
            line_count += 1
            if left == right:
                self_link_count += 1
            adjacency.setdefault(left, set()).add(right)
            adjacency.setdefault(right, set()).add(left)
        visited: Set[str] = set()
        sizes: List[int] = []
        for start in adjacency:
            if start in visited:
                continue
            component: Set[str] = set()
            stack = [start]
            while stack:
                current = stack.pop()
                if current in component:
                    continue
                component.add(current)
                stack.extend(adjacency.get(current, set()) - component)
            visited.update(component)
            sizes.append(len(component))
        degrees = sorted(len(neighbors) for neighbors in adjacency.values())
        return {
            "measured": True,
            "line_count": line_count,
            "named_node_count": len(adjacency),
            "component_count": len(sizes),
            "largest_component_size": max(sizes) if sizes else 0,
            "component_size_sample_desc": sorted(sizes, reverse=True)[:12],
            "degree_minimum": degrees[0] if degrees else 0,
            "degree_median": degrees[len(degrees) // 2] if degrees else 0,
            "degree_maximum": degrees[-1] if degrees else 0,
            "self_link_count": self_link_count,
        }

    def _constraint_endpoint_name_set(self, geometry: Any) -> Tuple[Set[str], bool]:
        """Return the exact constraint endpoint name set when point name is available."""
        name_attrib = _safe(lambda: geometry.findPointAttrib("name"), None)
        if name_attrib is None:
            return set(), False
        names: Set[str] = set()
        for point in (_safe(lambda: geometry.points(), ()) or ()):
            value = str(_safe(lambda point=point: point.attribValue(name_attrib), "") or "")
            if value:
                names.add(value)
        return names, True

    def _resolve_constraint_group(self, geometry: Any, expression: str) -> Tuple[List[Any], bool, str]:
        all_prims = list(_safe(lambda: geometry.prims(), ()) or ())
        if not expression.strip():
            return all_prims, True, "all_primitives"
        resolved = _safe(lambda: list(geometry.globPrims(expression)), None)
        if resolved is not None:
            return resolved, True, "hou.Geometry.globPrims"

        # Fallback for the common `groupA ^groupB` form used by Bullet rules.
        tokens = expression.split()
        if not tokens:
            return all_prims, True, "all_primitives"
        current: Optional[Set[Any]] = None
        exclude_next = False
        for token in tokens:
            if token == "^":
                exclude_next = True
                continue
            exclude = token.startswith("^") or exclude_next
            group_name = token[1:] if token.startswith("^") else token
            group = _safe(lambda group_name=group_name: geometry.findPrimGroup(group_name), None)
            if group is None:
                return [], False, "unresolved_group_token:%s" % group_name
            members = set(_safe(lambda group=group: group.prims(), ()) or ())
            if current is None:
                current = set(all_prims) if exclude else members
            elif exclude:
                current -= members
            else:
                current |= members
            exclude_next = False
        return list(current or set()), True, "simple_group_fallback"

    def _constraint_selection_summary(self, geometry: Any, prims: Sequence[Any]) -> Dict[str, Any]:
        return {
            "primitive_count": len(prims),
            "strength": self._numeric_primitive_summary(geometry, prims, "strength"),
            "propagate_rate": self._numeric_primitive_summary(geometry, prims, "propagate_rate"),
            "propagationiterations": self._numeric_primitive_summary(geometry, prims, "propagationiterations"),
            "impulse_halflife": self._numeric_primitive_summary(geometry, prims, "impulse_halflife"),
            "graph": self._constraint_graph_summary(geometry, prims),
        }

    def _diagnose_rbd_impact_topology(
        self,
        owner_path: str,
        constraints: GeometrySnapshot,
        geometry_snapshot: Optional[GeometrySnapshot],
        solver: Any,
    ) -> None:
        geometry = self._constraint_geo_object(constraints)
        if geometry is None:
            return
        all_prims = list(_safe(lambda: geometry.prims(), ()) or ())
        constraint_name_attrib = _safe(lambda: geometry.findPrimAttrib("constraint_name"), None)
        glue_prims = [
            prim
            for prim in all_prims
            if constraint_name_attrib is not None
            and str(_safe(lambda prim=prim: prim.attribValue(constraint_name_attrib), "") or "").lower() == "glue"
        ]
        all_graph = self._constraint_graph_summary(geometry, all_prims)
        geometry_name_count = None
        geometry_names: Set[str] = set()
        geometry_names_measured_exactly = False
        if geometry_snapshot is not None:
            name_stat = self._name_stat(geometry_snapshot)
            if name_stat is not None:
                geometry_name_count = name_stat.unique_count
                geometry_names_measured_exactly = name_stat.sampled == name_stat.count
                if geometry_names_measured_exactly:
                    geometry_names = {str(value) for value in name_stat.values if str(value)}
        constraint_endpoint_names, endpoint_names_measured_exactly = self._constraint_endpoint_name_set(geometry)
        geometry_without_constraint_endpoint: List[str] = []
        if geometry_names_measured_exactly and endpoint_names_measured_exactly:
            geometry_without_constraint_endpoint = sorted(geometry_names - constraint_endpoint_names)
        self.add_check(
            "RBD_CONSTRAINT_GRAPH_TOPOLOGY",
            "review",
            "rbd",
            owner_path,
            {
                "context": "solver_input_constraint_graph",
                "constraint_source": constraints.node_path,
                "geometry_unique_name_count": geometry_name_count,
                "geometry_and_endpoint_sets_measured_exactly": bool(
                    geometry_names_measured_exactly and endpoint_names_measured_exactly
                ),
                "geometry_names_without_constraint_endpoint_count": (
                    len(geometry_without_constraint_endpoint)
                    if geometry_names_measured_exactly and endpoint_names_measured_exactly
                    else None
                ),
                "geometry_names_without_constraint_endpoint_sample": geometry_without_constraint_endpoint[:12],
                "single_component_required_by_contract": False,
                "multiple_components_can_be_intentional_islands": True,
                "unconstrained_geometry_can_be_intentional_projectile_or_frame": True,
                "causal_effect_not_established": True,
                **all_graph,
            },
            "Graph成分数は構造測定です。単一成分であることを要求する契約ではありません。",
        )
        self.add_check(
            "RBD_GLUE_NUMERIC_DISTRIBUTION",
            "review",
            "rbd",
            owner_path,
            {
                "context": "solver_input_glue_primitives",
                "constraint_source": constraints.node_path,
                "static_distribution_only": True,
                "physical_cause_not_assigned": True,
                "requires_dynamic_response_measurement_for_behavior_claim": True,
                **self._constraint_selection_summary(geometry, glue_prims),
            },
            "Numeric distribution only; this check does not assign a physical cause.",
        )

        total_glue = len(glue_prims)
        glue_set = set(glue_prims)
        break_count = int(self._parm_value(solver, ("breaks",), 0) or 0)
        for index in range(1, break_count + 1):
            if not bool(self._parm_value(solver, ("constraint_useimpact%d" % index,), 0)):
                continue
            group_expression = self._parm_string(solver, ("constraint_group%d" % index,), "").strip()
            constraint_names = self._parm_string(solver, ("constraint_names%d" % index,), "").strip()
            selected, resolved, resolver = self._resolve_constraint_group(geometry, group_expression)
            if constraint_names:
                allowed_names = {token.casefold() for token in re.split(r"[\s,]+", constraint_names) if token}
                selected = [
                    prim
                    for prim in selected
                    if constraint_name_attrib is not None
                    and str(_safe(lambda prim=prim: prim.attribValue(constraint_name_attrib), "") or "").casefold() in allowed_names
                ]
            selected_set = set(selected)
            selected_glue = [prim for prim in selected if prim in glue_set]
            outside_glue = [prim for prim in glue_prims if prim not in selected_set]
            selected_summary = self._constraint_selection_summary(geometry, selected_glue)
            outside_summary = self._constraint_selection_summary(geometry, outside_glue)
            coverage = float(len(selected_glue)) / float(total_glue) if total_glue else None
            threshold = self._parm_value(solver, ("constraint_impactthreshold%d" % index,), None)
            evidence = {
                "context": "impact_break_rule_%d" % index,
                "rule_index": index,
                "constraint_names": constraint_names,
                "group_expression": group_expression,
                "group_resolved": resolved,
                "group_resolver": resolver,
                "impact_threshold": threshold,
                "total_glue_primitive_count": total_glue,
                "selected_glue_primitive_count": len(selected_glue),
                "outside_glue_primitive_count": len(outside_glue),
                "selected_glue_ratio": coverage,
                "selected": selected_summary,
                "outside": outside_summary,
            }
            self.add_check(
                "RBD_IMPACT_BREAK_RULE_SCOPE",
                "review" if resolved else "not_checked",
                "rbd",
                owner_path,
                evidence,
                "Measured rule scope and attributes; response is not simulated by this check.",
            )
            rate = selected_summary.get("propagate_rate", {})
            iterations = selected_summary.get("propagationiterations", {})
            graph = selected_summary.get("graph", {})
            localized_measurements = bool(
                resolved
                and selected_glue
                and coverage is not None
                and coverage < 0.60
                and isinstance(rate.get("maximum"), (int, float))
                and float(rate.get("maximum")) <= 0.05
                and isinstance(iterations.get("maximum"), (int, float))
                and float(iterations.get("maximum")) <= 3
            )
            if localized_measurements:
                self.add_issue(
                    "RBD_IMPACT_PROPAGATION_LOCALIZED",
                    "warning",
                    "high",
                    "rbd",
                    owner_path,
                    "Impact破壊ルールの対象範囲と伝播値が局所的です",
                    {
                        "rule_index": index,
                        "group_expression": group_expression,
                        "selected_glue_primitive_count": len(selected_glue),
                        "total_glue_primitive_count": total_glue,
                        "selected_glue_ratio": coverage,
                        "selected_graph_component_count": graph.get("component_count"),
                        "selected_graph_largest_component_size": graph.get("largest_component_size"),
                        "propagate_rate": rate,
                        "propagationiterations": iterations,
                        "outside_propagate_rate": outside_summary.get("propagate_rate", {}),
                    },
                    "衝撃が周辺へ伝わらない症状では、Impact対象Group、propagate_rate、propagationiterationsを確認してください。",
                    ["glue", "localized_impact"],
                )

    def _diagnose_rbd_sim_response_samples(self, solver: Any) -> None:
        path = _node_path(solver)
        frames = sorted({float(value) for value in self.compare_frames})[:6]
        samples: List[Dict[str, Any]] = []
        collider_connection = next(
            (
                connection
                for connection in (_safe(lambda: solver.inputConnections(), ()) or ())
                if int(_safe(lambda connection=connection: connection.inputIndex(), -1)) == 3
            ),
            None,
        )
        collider_node = _safe(lambda: collider_connection.inputNode(), None) if collider_connection is not None else None
        collider_output = int(_safe(lambda: collider_connection.outputIndex(), 0) or 0) if collider_connection is not None else 0

        def percentile(values: Sequence[float], fraction: float) -> float:
            if not values:
                return 0.0
            ordered = sorted(float(value) for value in values)
            return ordered[min(len(ordered) - 1, int((len(ordered) - 1) * fraction))]

        for frame in frames:
            try:
                hou.setFrame(frame)
                piece_geometry = solver.geometry(0)
                constraint_geometry = solver.geometry(1)
            except Exception as exc:
                samples.append({"frame": frame, "measured": False, "error": "%s: %s" % (exc.__class__.__name__, exc)})
                continue
            velocity_attrib = _safe(lambda: piece_geometry.findPointAttrib("v"), None)
            name_attrib = _safe(lambda: piece_geometry.findPointAttrib("name"), None)
            active_attrib = _safe(lambda: piece_geometry.findPointAttrib("active"), None)
            speeds: List[float] = []
            active_speeds: List[float] = []
            velocity_vectors: List[Tuple[float, float, float]] = []
            moving_names: List[str] = []
            active_count = 0
            for point in list(_safe(lambda: piece_geometry.points(), ()) or ()):
                velocity = _safe(lambda point=point: point.attribValue(velocity_attrib), (0.0, 0.0, 0.0)) if velocity_attrib is not None else (0.0, 0.0, 0.0)
                velocity_tuple = tuple(float(value) for value in tuple(velocity)[:3])
                speed = _vector_length(velocity) or 0.0
                speeds.append(speed)
                velocity_vectors.append(velocity_tuple)
                if speed > 0.01 and name_attrib is not None and len(moving_names) < 20:
                    moving_names.append(str(_safe(lambda point=point: point.attribValue(name_attrib), "") or ""))
                if active_attrib is not None and bool(_safe(lambda point=point: point.attribValue(active_attrib), 0)):
                    active_count += 1
                    active_speeds.append(speed)
            constraint_prims = list(_safe(lambda: constraint_geometry.prims(), ()) or ())
            collider_positions: Dict[str, Tuple[float, float, float]] = {}
            collider_explicit_speeds: List[float] = []
            collider_speedmax_values: List[float] = []
            if collider_node is not None:
                collider_geometry = _safe(lambda: collider_node.geometryAtFrame(frame, collider_output), None)
                if collider_geometry is not None:
                    collider_name = _safe(lambda: collider_geometry.findPointAttrib("name"), None)
                    collider_velocity = _safe(lambda: collider_geometry.findPointAttrib("v"), None)
                    collider_speedmax = _safe(lambda: collider_geometry.findPointAttrib("speedmax"), None)
                    for point_index, point in enumerate(list(_safe(lambda: collider_geometry.points(), ()) or ())):
                        key = (
                            str(_safe(lambda point=point: point.attribValue(collider_name), "") or "")
                            if collider_name is not None
                            else "@point%d" % point_index
                        )
                        if not key:
                            key = "@point%d" % point_index
                        collider_positions[key] = tuple(float(value) for value in tuple(point.position())[:3])
                        explicit_velocity = (
                            _safe(lambda point=point: point.attribValue(collider_velocity), (0.0, 0.0, 0.0))
                            if collider_velocity is not None
                            else (0.0, 0.0, 0.0)
                        )
                        collider_explicit_speeds.append(_vector_length(explicit_velocity) or 0.0)
                        if collider_speedmax is not None:
                            collider_speedmax_values.append(
                                float(_safe(lambda point=point: point.attribValue(collider_speedmax), 0.0) or 0.0)
                            )
            samples.append(
                {
                    "frame": frame,
                    "measured": True,
                    "piece_count": len(speeds),
                    "active_piece_count": active_count if active_attrib is not None else None,
                    "moving_piece_count_speed_gt_0_01": sum(value > 0.01 for value in speeds),
                    "moving_piece_count_speed_gt_0_1": sum(value > 0.1 for value in speeds),
                    "maximum_speed": max(speeds) if speeds else None,
                    "active_speed_p50": percentile(active_speeds, 0.50),
                    "active_speed_p90": percentile(active_speeds, 0.90),
                    "active_speed_p99": percentile(active_speeds, 0.99),
                    "moving_fraction_of_active": (
                        sum(value > 0.01 for value in active_speeds) / float(active_count)
                        if active_count > 0
                        else None
                    ),
                    "velocity_x_positive_count_speed_gt_0_01": sum(
                        speed > 0.01 and velocity[0] > 0.01
                        for speed, velocity in zip(speeds, velocity_vectors)
                    ),
                    "velocity_x_negative_count_speed_gt_0_01": sum(
                        speed > 0.01 and velocity[0] < -0.01
                        for speed, velocity in zip(speeds, velocity_vectors)
                    ),
                    "moving_name_sample": moving_names,
                    "constraint_primitive_count": len(constraint_prims),
                    "constraint_strength": self._numeric_primitive_summary(constraint_geometry, constraint_prims, "strength"),
                    "constraint_graph": self._constraint_graph_summary(constraint_geometry, constraint_prims),
                    "collider_explicit_v_present": bool(collider_explicit_speeds),
                    "collider_explicit_v_nonzero_count": sum(value > 1e-5 for value in collider_explicit_speeds),
                    "collider_explicit_v_maximum": max(collider_explicit_speeds) if collider_explicit_speeds else None,
                    "collider_speedmax_attribute_minimum": min(collider_speedmax_values) if collider_speedmax_values else None,
                    "collider_speedmax_attribute_maximum": max(collider_speedmax_values) if collider_speedmax_values else None,
                    "_piece_velocity_vectors": velocity_vectors,
                    "_collider_positions": collider_positions,
                }
            )
        measured = [sample for sample in samples if sample.get("measured")]
        collider_zero_v_motion: List[Dict[str, Any]] = []
        opposite_motion_samples: List[Dict[str, Any]] = []
        if measured:
            baseline = measured[0]
            base_constraints = int(baseline.get("constraint_primitive_count", 0) or 0)
            for sample in measured:
                sample["constraint_count_change_from_first_sample"] = int(sample.get("constraint_primitive_count", 0) or 0) - base_constraints
            for previous, current in zip(measured[:-1], measured[1:]):
                previous_positions = previous.get("_collider_positions") or {}
                current_positions = current.get("_collider_positions") or {}
                common_names = sorted(set(previous_positions) & set(current_positions))
                frame_delta = float(current.get("frame", 0.0)) - float(previous.get("frame", 0.0))
                seconds = frame_delta / float(_safe(lambda: hou.fps(), 24.0) or 24.0)
                motions: List[Tuple[float, str, Tuple[float, float, float]]] = []
                if seconds > 0:
                    for name in common_names:
                        vector = tuple(
                            (float(current_positions[name][axis]) - float(previous_positions[name][axis])) / seconds
                            for axis in range(3)
                        )
                        motions.append((_vector_length(vector) or 0.0, name, vector))
                if not motions:
                    continue
                motions.sort(key=lambda item: item[0])
                maximum_motion = motions[-1]
                motion_record = {
                    "from_frame": previous.get("frame"),
                    "to_frame": current.get("frame"),
                    "matched_point_count": len(motions),
                    "implied_speed_p50": percentile([item[0] for item in motions], 0.50),
                    "implied_speed_p90": percentile([item[0] for item in motions], 0.90),
                    "implied_speed_maximum": maximum_motion[0],
                    "fastest_point_name": maximum_motion[1],
                    "fastest_point_velocity": list(maximum_motion[2]),
                    "explicit_v_maximum_at_to_frame": current.get("collider_explicit_v_maximum"),
                    "speedmax_attribute_maximum_at_to_frame": current.get("collider_speedmax_attribute_maximum"),
                }
                current["collider_position_motion_from_previous_sample"] = motion_record
                if maximum_motion[0] > 0.1 and float(current.get("collider_explicit_v_maximum", 0.0) or 0.0) <= 1e-5:
                    collider_zero_v_motion.append(motion_record)
                driver_length = maximum_motion[0]
                piece_vectors = current.get("_piece_velocity_vectors") or []
                if driver_length > 1e-5 and piece_vectors:
                    unit = tuple(value / driver_length for value in maximum_motion[2])
                    aligned: List[float] = []
                    opposite_speeds: List[float] = []
                    for vector in piece_vectors:
                        speed = _vector_length(vector) or 0.0
                        if speed <= 0.01:
                            continue
                        dot = sum(vector[axis] * unit[axis] for axis in range(3))
                        aligned.append(dot)
                        if dot < -0.01:
                            opposite_speeds.append(speed)
                    alignment_record = {
                        "driver_point_name": maximum_motion[1],
                        "driver_velocity": list(maximum_motion[2]),
                        "moving_piece_count": len(aligned),
                        "along_driver_count": sum(value > 0.01 for value in aligned),
                        "opposite_driver_count": sum(value < -0.01 for value in aligned),
                        "opposite_driver_ratio": (
                            sum(value < -0.01 for value in aligned) / float(len(aligned))
                            if aligned
                            else None
                        ),
                        "opposite_piece_speed_p90": percentile(opposite_speeds, 0.90),
                    }
                    current["piece_velocity_alignment_to_fastest_collider_point"] = alignment_record
                    if (
                        aligned
                        and len(opposite_speeds) >= max(10, int(len(aligned) * 0.10))
                        and percentile(opposite_speeds, 0.90) > 1.0
                        and float(current.get("active_speed_p50", 0.0) or 0.0)
                        / max(float(previous.get("active_speed_p50", 0.0) or 0.0), 0.01) >= 10.0
                    ):
                        opposite_motion_samples.append({"frame": current.get("frame"), **alignment_record})
        for sample in samples:
            sample.pop("_piece_velocity_vectors", None)
            sample.pop("_collider_positions", None)
        self.add_check(
            "RBD_SIM_RESPONSE_SAMPLE",
            "review" if measured else "not_checked",
            "rbd",
            path,
            {
                "context": "explicit_deep_compare_frames",
                "samples": samples,
                "frames_requested": frames,
                "simulation_was_cooked": bool(measured),
            },
            "These are frame samples, not a causal interpretation.",
        )
        if collider_zero_v_motion:
            self.add_issue(
                "RBD_COLLIDER_POSITION_MOTION_WITH_ZERO_V",
                "warning",
                "high",
                "rbd",
                path,
                "ColliderのP移動を測定しましたが明示vは0のままです",
                {
                    "observed_intervals": collider_zero_v_motion,
                    "position_motion_and_explicit_v_measured": True,
                    "solver_derived_motion_behavior_not_established": True,
                },
                "Input 4のAnimated/Deforming方式と速度生成を確認し、Speed Max属性だけでP移動が制限されたと仮定しないでください。",
                ["violent_fragments", "tunneling", "collision_offset"],
            )
        if opposite_motion_samples:
            self.add_issue(
                "RBD_SIM_RESPONSE_OPPOSITE_COLLIDER_MOTION",
                "warning",
                "high",
                "rbd",
                path,
                "Collider主要移動方向と逆向きのPiece速度を比較フレームで測定しました",
                {
                    "observed_samples": opposite_motion_samples,
                    "contact_normal_and_causal_mechanism_not_measured": True,
                },
                "深いめり込み、固定境界からの反力、Bounce、Collider速度生成を分けて確認してください。",
                ["violent_fragments"],
            )
        if len(measured) < 2:
            return
        future_samples = measured[1:]
        if future_samples:
            no_motion_samples = [
                {
                    "frame": sample.get("frame"),
                    "piece_count": sample.get("piece_count"),
                    "active_piece_count": sample.get("active_piece_count"),
                    "moving_piece_count_speed_gt_0_01": sample.get("moving_piece_count_speed_gt_0_01"),
                    "maximum_speed": sample.get("maximum_speed"),
                    "constraint_primitive_count": sample.get("constraint_primitive_count"),
                }
                for sample in future_samples
                if int(sample.get("moving_piece_count_speed_gt_0_01", 0) or 0) == 0
                and float(sample.get("maximum_speed", 0.0) or 0.0) <= 0.01
            ]
            if len(no_motion_samples) == len(future_samples):
                self.add_issue(
                    "RBD_SIM_RESPONSE_NO_MOTION",
                    "error",
                    "high",
                    "rbd",
                    path,
                    "比較した将来フレームで移動Pieceを検出できませんでした",
                    {
                        "first_sample_frame": measured[0].get("frame"),
                        "observed_future_samples": no_motion_samples,
                        "speed_threshold": 0.01,
                        "simulation_was_cooked": True,
                    },
                    "Solver入力のactive/animated分布、RBD ConfigureのUse Bounds被覆、Colliderとの位置関係を確認してください。",
                    ["no_motion", "rbd_general"],
                )
        widespread_speed_samples: List[Dict[str, Any]] = []
        for previous, current in zip(measured[:-1], measured[1:]):
            active_count = int(current.get("active_piece_count", 0) or 0)
            moving_fraction = current.get("moving_fraction_of_active")
            current_median = float(current.get("active_speed_p50", 0.0) or 0.0)
            previous_median = float(previous.get("active_speed_p50", 0.0) or 0.0)
            gain_ratio = current_median / max(previous_median, 0.01)
            if (
                active_count >= 20
                and isinstance(moving_fraction, (int, float))
                and float(moving_fraction) >= 0.80
                and current_median > 5.0
                and gain_ratio >= 10.0
            ):
                widespread_speed_samples.append(
                    {
                        "from_frame": previous.get("frame"),
                        "frame": current.get("frame"),
                        "piece_count": current.get("piece_count"),
                        "active_piece_count": active_count,
                        "moving_fraction_of_active": moving_fraction,
                        "previous_active_speed_p50": previous_median,
                        "active_speed_p50": current_median,
                        "active_speed_p90": current.get("active_speed_p90"),
                        "active_speed_p99": current.get("active_speed_p99"),
                        "maximum_speed": current.get("maximum_speed"),
                        "median_speed_gain_ratio": gain_ratio,
                        "previous_constraint_count": previous.get("constraint_primitive_count"),
                        "constraint_count": current.get("constraint_primitive_count"),
                    }
                )
        if widespread_speed_samples:
            self.add_issue(
                "RBD_SIM_RESPONSE_WIDESPREAD_SPEED_SPIKE",
                "warning",
                "high",
                "rbd",
                path,
                "多数のActive Pieceで急激な速度上昇を比較フレームから測定しました",
                {
                    "observed_samples": widespread_speed_samples,
                    "absolute_speed_is_scene_scale_dependent": True,
                    "causal_mechanism_not_established": True,
                },
                "Colliderのフレーム間P移動、明示v、めり込み、固定境界、Constraint解除タイミングを確認してください。",
                ["violent_fragments"],
            )
        baseline_constraint_count = int(measured[0].get("constraint_primitive_count", 0) or 0)
        localized_samples = []
        for sample in measured[1:]:
            piece_count = int(sample.get("piece_count", 0) or 0)
            moving_count = int(sample.get("moving_piece_count_speed_gt_0_01", 0) or 0)
            remaining_constraints = int(sample.get("constraint_primitive_count", 0) or 0)
            graph = sample.get("constraint_graph") or {}
            removed = baseline_constraint_count - remaining_constraints
            largest = int(graph.get("largest_component_size", 0) or 0)
            if removed > 0 and piece_count > 0 and moving_count <= max(10, int(piece_count * 0.05)) and largest >= int(piece_count * 0.90):
                localized_samples.append(
                    {
                        "frame": sample.get("frame"),
                        "constraints_removed_from_first_sample": removed,
                        "moving_piece_count_speed_gt_0_01": moving_count,
                        "piece_count": piece_count,
                        "remaining_graph_component_count": graph.get("component_count"),
                        "remaining_graph_largest_component_size": largest,
                    }
                )
        if localized_samples:
            self.add_issue(
                "RBD_SIM_RESPONSE_FEW_MOVING_PIECES",
                "warning",
                "high",
                "rbd",
                path,
                "比較フレームでConstraint減少に対して移動Piece数が少ない状態を測定しました",
                {
                    "first_sample_frame": measured[0].get("frame"),
                    "first_sample_constraint_count": baseline_constraint_count,
                    "observed_samples": localized_samples,
                },
                "Impact Groupと伝播属性、残存Constraint graphを確認してください。",
                ["glue", "localized_impact"],
            )

    def _diagnose_constraint_geometry(
        self,
        owner_path: str,
        constraints: GeometrySnapshot,
        geometry: Optional[GeometrySnapshot],
    ) -> None:
        constraint_name = constraints.stat("primitive", "constraint_name")
        strength = constraints.stat("primitive", "strength")
        primitive_count = constraints.counts.get("primitives", 0)
        glue_present = bool(
            constraint_name is not None
            and any(str(value).lower() == "glue" for value in constraint_name.values)
        )
        schema_ok = bool(constraint_name is not None and (not glue_present or strength is not None))
        self.add_check(
            "RBD_CONSTRAINT_PRIMITIVE_SCHEMA",
            "pass" if schema_ok else "fail",
            "rbd",
            owner_path,
            {
                "context": "constraint_geometry",
                "constraint_source": constraints.node_path,
                "primitive_count": primitive_count,
                "constraint_name_present": constraint_name is not None,
                "glue_observed_in_sample": glue_present,
                "strength_present": strength is not None,
            },
        )
        role_complete = constraints.primitive_role_sampled == primitive_count
        two_point_lines = constraints.two_endpoint_open_line_count
        role_ok = bool(
            role_complete
            and primitive_count > 0
            and two_point_lines == primitive_count
            and constraints.closed_polygon_primitive_count == 0
        )
        self.add_check(
            "RBD_CONSTRAINT_GEOMETRY_ROLE",
            "pass" if role_ok else "review",
            "rbd",
            owner_path,
            {
                "context": "constraint_geometry_role",
                "constraint_source": constraints.node_path,
                "primitive_count": primitive_count,
                "two_endpoint_open_line_count": two_point_lines,
                "open_polyline_count": constraints.open_polyline_primitive_count,
                "closed_polygon_count": constraints.closed_polygon_primitive_count,
                "role_sample_complete": role_complete,
                "zero_surface_area_is_expected_for_open_lines": True,
            },
        )
        if primitive_count and len(constraints.primitive_pairs) < primitive_count * 0.9:
            self.add_issue(
                "RBD_CONSTRAINT_NONLINE_PRIMITIVES",
                "warning",
                "high",
                "rbd",
                owner_path,
                "Constraint Geometryに2端点LineではないPrimitiveが多数あります",
                {"primitives": primitive_count, "two_endpoint_lines": len(constraints.primitive_pairs)},
                "Constraint Branchへ表示Geometryが混入していないか確認してください。",
                ["glue", "frame_one_explosion"],
            )
        if constraint_name is None:
            self.add_issue(
                "RBD_CONSTRAINT_NAME_MISSING",
                "error",
                "high",
                "rbd",
                owner_path,
                "Constraint Primitiveにconstraint_nameがありません",
                {"source": constraints.node_path},
                "RBD Constraint PropertiesでGlue等のConstraint Typeを設定してください。",
                ["glue"],
            )
        if strength is None and glue_present:
            self.add_issue(
                "RBD_GLUE_STRENGTH_MISSING",
                "error",
                "high",
                "rbd",
                owner_path,
                "Glue Constraintにstrengthがありません",
                suggestion="RBD Constraint PropertiesでGlue Strengthを設定してください。",
                symptoms=["glue"],
            )
        if strength is not None:
            if strength.zero_count and strength.sampled == strength.count and strength.zero_count == strength.sampled:
                self.add_issue(
                    "RBD_ALL_GLUE_ZERO_STRENGTH",
                    "error",
                    "high",
                    "rbd",
                    owner_path,
                    "すべてのConstraint strengthが0です",
                    {"count": strength.zero_count},
                    "意図しない全Glue解除や式の評価失敗を確認してください。",
                    ["glue"],
                )
            if strength.maximum is not None and abs(strength.maximum) > 1e20:
                self.add_issue(
                    "RBD_EXTREME_GLUE_STRENGTH",
                    "warning",
                    "high",
                    "rbd",
                    owner_path,
                    "Glue strengthが極端に大きいです",
                    {"maximum": strength.maximum},
                    "ワールドスケールとstrengthの単位補正を確認してください。",
                    ["glue"],
                )

        pair_counts: Dict[Tuple[str, str], int] = {}
        self_pairs = 0
        for left, right in constraints.primitive_pairs:
            if not left or not right:
                continue
            if left == right:
                self_pairs += 1
            key = tuple(sorted((left, right)))
            pair_counts[key] = pair_counts.get(key, 0) + 1
        duplicate_pairs = sum(count - 1 for count in pair_counts.values() if count > 1)
        if self_pairs:
            self.add_issue(
                "RBD_CONSTRAINT_SELF_LINKS",
                "error",
                "high",
                "rbd",
                owner_path,
                "同じピース自身を結ぶConstraintがあります",
                {"count": self_pairs},
                "Constraint生成前後のnameと近接検索を確認してください。",
                ["frame_one_explosion", "glue"],
            )
        if duplicate_pairs:
            self.add_issue(
                "RBD_DUPLICATE_CONSTRAINT_PAIRS",
                "warning",
                "high",
                "rbd",
                owner_path,
                "同じ2ピース間の重複Constraintがあります",
                {"duplicate_count": duplicate_pairs},
                "複数Constraint生成BranchのMergeと重複除去を確認してください。",
                ["glue", "performance"],
            )

        if geometry is not None:
            piece_count = max(1, self._name_stat(geometry).unique_count or geometry.counts.get("points", 1))
            constraint_count = constraints.counts.get("primitives", 0)
            ratio = float(constraint_count) / float(piece_count)
            if ratio > 40:
                self.add_issue(
                    "RBD_CONSTRAINT_DENSITY_HIGH",
                    "warning",
                    "high",
                    "performance",
                    owner_path,
                    "ピース数に対してConstraintが過剰です",
                    {"pieces": piece_count, "constraints": constraint_count, "constraints_per_piece": ratio},
                    "Search Radius、最大近傍数、重複Constraintを確認してください。",
                    ["performance", "glue"],
                )
            scene_diagonal = float(geometry.bbox.get("diagonal", 0.0) or 0.0)
            if scene_diagonal > 0 and constraints.primitive_diagonals:
                long_count = sum(1 for value in constraints.primitive_diagonals if value > scene_diagonal * 0.25)
                if long_count:
                    self.add_issue(
                        "RBD_LONG_CONSTRAINTS",
                        "warning",
                        "high",
                        "rbd",
                        owner_path,
                        "シーン寸法に対して長すぎるConstraintがあります",
                        {
                            "count_sampled": long_count,
                            "sampled": len(constraints.primitive_diagonals),
                            "scene_diagonal": scene_diagonal,
                            "max_constraint_length": max(constraints.primitive_diagonals),
                        },
                        "Search Radius、Constraint端点P、異なるScaleのMergeを確認してください。",
                        ["frame_one_explosion", "glue"],
                    )

    def _diagnose_rbd_piece_attributes(
        self,
        owner_path: str,
        geometry: GeometrySnapshot,
        solver: Any,
    ) -> None:
        active = geometry.stat("point", "active")
        animated = geometry.stat("point", "animated")
        friction = geometry.stat("point", "friction")
        bounce = geometry.stat("point", "bounce")
        density = geometry.stat("point", "density")
        pscale = geometry.stat("point", "pscale")
        orient = geometry.stat("point", "orient")

        if active is not None and active.positive_count == 0 and active.sampled:
            source_node = _safe(lambda: hou.node(geometry.node_path), None) if hou is not None else None
            upstream_time_paths = self._upstream_time_dependent_paths(source_node)
            scan_is_start_frame = abs(float(geometry.frame) - float(self.start_frame)) < 1e-6
            future_compare_frames = sorted(float(frame) for frame in self.compare_frames if float(frame) > float(geometry.frame))
            active_evidence = {
                "context": "solver_input_active_at_scan_frame",
                "frame": geometry.frame,
                "start_frame": self.start_frame,
                "scan_is_start_frame": scan_is_start_frame,
                "piece_count": active.sampled,
                "active_positive_count": active.positive_count,
                "upstream_time_dependent_count": len(upstream_time_paths),
                "upstream_time_dependent_sample": upstream_time_paths[:12],
                "future_compare_frames": future_compare_frames,
                "future_activation_measured_by_this_check": False,
                "causal_effect_on_impact_not_measured_by_this_check": True,
            }
            self.add_check(
                "RBD_ACTIVE_STATE_AT_SCAN_FRAME",
                "review",
                "rbd",
                owner_path,
                active_evidence,
                "Single-frame state only; use Deep compare frames to measure later activation.",
            )
            if not upstream_time_paths and not future_compare_frames:
                self.add_issue(
                    "RBD_ALL_PIECES_INACTIVE_WITHOUT_OBSERVED_UPDATE",
                    "warning",
                    "medium",
                    "rbd",
                    owner_path,
                    "走査フレームで全ピースがactive=0で、上流の時間依存更新を確認できません",
                    active_evidence,
                    "別フレームでactiveを比較し、意図したHoldか未設定かを確認してください。",
                    ["rbd_general", "glue"],
                )
        if active is not None and animated is not None and active.sampled == animated.sampled:
            both = 0
            for left, right in zip(active.values, animated.values):
                if bool(left) and bool(right):
                    both += 1
            if both:
                self.add_issue(
                    "RBD_ACTIVE_ANIMATED_OVERLAP",
                    "warning",
                    "medium",
                    "rbd",
                    owner_path,
                    "active=1かつanimated=1のピースがあります",
                    {"count": both, "sampled": active.sampled},
                    "動的ピースかキネマティックピースかを明確に分けてください。",
                    ["frame_one_explosion", "rbd_general"],
                )
        if friction is not None and friction.maximum is not None:
            if friction.maximum < 0.08:
                below_count = sum(
                    1 for value in friction.values
                    if isinstance(value, (int, float)) and float(value) < 0.08
                )
                self.add_issue(
                    "RBD_VERY_LOW_FRICTION",
                    "info",
                    "high",
                    "rbd",
                    owner_path,
                    "入力frictionが低摩擦ヒューリスティック範囲です",
                    {
                        "minimum": friction.minimum,
                        "maximum": friction.maximum,
                        "below_0_08_count": below_count,
                        "sampled_count": friction.sampled,
                        "sample_is_complete": friction.sampled == friction.count,
                        "heuristic_only": True,
                        "visual_problem_not_established": True,
                        "causal_effect_not_established": True,
                    },
                    "滑りが症状として観測された場合だけ、入力Point Attributeの最終値と接触材質を確認してください。",
                    ["sliding"],
                )
            solver_friction = self._parm_value(solver, ("friction",), None)
            if isinstance(solver_friction, (int, float)) and friction.minimum is not None:
                if abs(float(solver_friction) - float(friction.minimum)) > 0.25:
                    self.add_issue(
                        "RBD_FRICTION_ATTRIBUTE_OVERRIDES_SOLVER",
                        "notice",
                        "high",
                        "rbd",
                        owner_path,
                        "入力friction属性とSolver既定摩擦が大きく異なります",
                        {
                            "solver_friction": solver_friction,
                            "input_min": friction.minimum,
                            "input_max": friction.maximum,
                        },
                        "Point AttributeがSolver既定値を上書きする構成か確認してください。",
                        ["sliding"],
                    )
        if bounce is not None and bounce.maximum is not None and bounce.maximum > 0.8:
            self.add_issue(
                "RBD_HIGH_BOUNCE",
                "warning",
                "high",
                "rbd",
                owner_path,
                "RBDピースのbounceが高いです",
                {"maximum": bounce.maximum},
                "ガラスやコンクリートがゴムのように跳ねる場合は下げてください。",
                ["bouncing"],
            )
        if density is not None and density.minimum is not None and density.minimum <= 0:
            self.add_issue(
                "RBD_NONPOSITIVE_DENSITY",
                "error",
                "high",
                "rbd",
                owner_path,
                "0以下のdensityがあります",
                {"minimum": density.minimum},
                "正の密度を設定してください。",
                ["frame_one_explosion"],
            )
        if pscale is not None and pscale.minimum is not None and pscale.minimum <= 0:
            self.add_issue(
                "RBD_NONPOSITIVE_PSCALE",
                "error",
                "high",
                "rbd",
                owner_path,
                "0以下のpscaleがあります",
                {"minimum": pscale.minimum},
                "ゼロまたは負ScaleのPackedピースを修正してください。",
                ["frame_one_explosion", "collision_offset"],
            )
        if orient is not None and orient.values:
            bad_quaternions = 0
            for value in orient.values:
                length = _vector_length(value)
                if length is not None and abs(length - 1.0) > 0.05:
                    bad_quaternions += 1
            if bad_quaternions:
                self.add_issue(
                    "RBD_ORIENT_NOT_NORMALIZED",
                    "warning",
                    "high",
                    "rbd",
                    owner_path,
                    "正規化されていないorientがあります",
                    {"count": bad_quaternions, "sampled": orient.sampled},
                    "QuaternionをNormalizeし、ゼロQuaternionを除去してください。",
                    ["frame_one_explosion", "collision_offset"],
                )

        margins = geometry.stat("point", "bullet_collision_margin")
        if margins is not None and margins.maximum is not None and geometry.primitive_min_dimensions:
            sorted_dims = sorted(geometry.primitive_min_dimensions)
            median = sorted_dims[len(sorted_dims) // 2]
            if median > 0 and margins.maximum / median > 0.25:
                self.add_issue(
                    "RBD_COLLISION_MARGIN_LARGE_RELATIVE_TO_PIECE",
                    "warning",
                    "high",
                    "rbd",
                    owner_path,
                    "Collision Marginがピース寸法に対して大きいです",
                    {"margin_max": margins.maximum, "median_min_piece_dimension": median, "ratio": margins.maximum / median},
                    "小規模シーンではMarginとShrink Amountを長さスケールに合わせてください。",
                    ["frame_one_explosion", "rbd_general"],
                )
        scene_diagonal = float(geometry.bbox.get("diagonal", 0.0) or 0.0)
        if scene_diagonal > 0 and geometry.primitive_min_dimensions:
            tiny_threshold = scene_diagonal * 1e-6
            tiny_count = sum(1 for value in geometry.primitive_min_dimensions if value < tiny_threshold)
            if tiny_count > max(10, len(geometry.primitive_min_dimensions) * 0.05):
                self.add_issue(
                    "RBD_MANY_TINY_PIECES",
                    "warning",
                    "medium",
                    "rbd",
                    owner_path,
                    "全体スケールに対して極小の破片が多くあります",
                    {
                        "tiny_count_sampled": tiny_count,
                        "sampled": len(geometry.primitive_min_dimensions),
                        "threshold": tiny_threshold,
                    },
                    "Fractureの最小サイズ、Scatter密度、Tiny Pieces削除を検討してください。",
                    ["performance", "frame_one_explosion"],
                )

    def _diagnose_initial_rbd_state(self, owner_path: str, geometry: GeometrySnapshot) -> None:
        names = geometry.stat("point", "name")
        for name in ("v", "w"):
            stat = geometry.stat("point", name)
            if stat is None or stat.vector_max_length is None:
                continue
            moving = sum(1 for value in stat.values if (_vector_length(value) or 0.0) > 1e-5)
            if moving:
                sampled = max(1, stat.sampled)
                sparse_limit = max(2, int(sampled * 0.001))
                sparse_initial_motion = moving <= sparse_limit
                moving_names: List[str] = []
                if names is not None and len(names.values) == len(stat.values):
                    for piece_name, value in zip(names.values, stat.values):
                        if (_vector_length(value) or 0.0) > 1e-5:
                            moving_names.append(str(piece_name))
                self.add_issue(
                    "RBD_NONZERO_INITIAL_" + name.upper(),
                    "info" if sparse_initial_motion else "warning",
                    "high",
                    "rbd",
                    owner_path,
                    "開始フレームで非ゼロ%sを測定" % name,
                    {
                        "frame": geometry.frame,
                        "moving_count": moving,
                        "sampled": stat.sampled,
                        "moving_fraction": moving / float(sampled),
                        "sparse_initial_motion": sparse_initial_motion,
                        "max_length": stat.vector_max_length,
                        "moving_name_sample": moving_names[:12],
                        "sample_is_complete": stat.sampled == stat.count,
                        "causal_effect_not_established": True,
                    },
                    "投射物など意図した初速かをnameで分類してください。多数の破片に分布する場合は残留値も確認してください。",
                    ["frame_one_explosion"],
                )

    def _diagnose_external_collider(
        self,
        owner_path: str,
        collider: GeometrySnapshot,
        solver: Any,
    ) -> None:
        velocity = collider.stat("point", "v")
        substeps = self._parm_value(solver, ("substep", "substeps"), 1)
        if velocity is not None and velocity.vector_max_length is not None and velocity.vector_max_length > 20:
            severity = "warning" if float(substeps or 1) < 4 else "notice"
            self.add_issue(
                "RBD_FAST_EXTERNAL_COLLIDER",
                severity,
                "high",
                "rbd",
                owner_path,
                "外部コライダーの速度が高いです",
                {"max_speed": velocity.vector_max_length, "substeps": substeps, "source": collider.node_path},
                "Collider側へSpeed Maxを設定し、必要に応じてSubstepsを増やしてください。",
                ["tunneling", "violent_fragments"],
            )
        deforming = collider.any_stat("deforming")
        animated = collider.any_stat("animated")
        if deforming is None and animated is None:
            source_node = _safe(lambda: hou.node(collider.node_path), None) if hou is not None else None
            upstream_time_paths = self._upstream_time_dependent_paths(source_node)
            evidence = {
                "context": "external_collider_motion_inputs",
                "source": collider.node_path,
                "motion_flag_attributes_present": False,
                "upstream_time_dependent_count": len(upstream_time_paths),
                "upstream_time_dependent_sample": upstream_time_paths[:12],
                "upstream_time_dependency_present": bool(upstream_time_paths),
                "collider_motion_state": "not_measured",
                "missing_motion_flags_do_not_establish_static_collider": True,
                "collision_response_not_measured_by_this_check": True,
            }
            self.add_check(
                "RBD_COLLIDER_MOTION_INPUT_EVIDENCE",
                "review",
                "rbd",
                owner_path,
                evidence,
                "Missing point/primitive flags alone does not establish that input 4 is static.",
            )
            if not upstream_time_paths:
                self.add_issue(
                    "RBD_COLLIDER_MOTION_FLAGS_MISSING_WITHOUT_TIME_DEPENDENCY",
                    "notice",
                    "medium",
                    "rbd",
                    owner_path,
                    "Colliderのmotion属性と上流時間依存を確認できません",
                    evidence,
                    "静止Colliderなら問題ありません。変形キャラクターなら入力4の時間変化を比較してください。",
                    ["tunneling", "collision_offset"],
                )

    def _diagnose_breaking_thresholds(self, solver: Any) -> None:
        path = _node_path(solver)
        count = int(self._parm_value(solver, ("breaks",), 0) or 0)
        for index in range(1, count + 1):
            use_at_frame = bool(self._parm_value(solver, ("constraint_useatframe%d" % index,), 0))
            group = self._parm_string(solver, ("constraint_group%d" % index,), "").strip()
            constraint_name = self._parm_string(solver, ("constraint_names%d" % index,), "").strip()
            if use_at_frame and not group:
                frame = self._parm_value(solver, ("constraint_atframe%d" % index,), None)
                observed_frames = [self.original_frame] + list(self.compare_frames)
                observed_max = max(observed_frames) if observed_frames else self.original_frame
                within_observed_window = bool(isinstance(frame, (int, float)) and float(frame) <= float(observed_max))
                event_reached_at_scan_frame = bool(
                    isinstance(frame, (int, float)) and float(self.original_frame) >= float(frame)
                )
                schedule_evidence = {
                    "context": "at_frame_break_schedule",
                    "rule_index": index,
                    "constraint_name": constraint_name,
                    "at_frame": frame,
                    "scan_frame": self.original_frame,
                    "compare_frame_maximum": max(self.compare_frames) if self.compare_frames else None,
                    "within_observed_frame_window": within_observed_window,
                    "event_reached_at_scan_frame": event_reached_at_scan_frame,
                    "rule_does_not_execute_before_at_frame": True,
                }
                self.add_check(
                    "RBD_AT_FRAME_BREAK_SCHEDULE",
                    "review",
                    "rbd",
                    path,
                    schedule_evidence,
                    "Schedule measurement only; a future At Frame event does not execute at the scan frame.",
                )
                if within_observed_window:
                    self.add_issue(
                        "RBD_GLOBAL_AT_FRAME_BREAK_WITHIN_OBSERVED_WINDOW",
                        "warning",
                        "high",
                        "rbd",
                        path,
                        "観測フレーム範囲内にGroup未指定のAt Frame破壊があります",
                        schedule_evidence,
                        "意図した全体解除か、局所Groupが必要かを確認してください。",
                        ["glue", "clock_driven_break"],
                    )
            use_impact = bool(self._parm_value(solver, ("constraint_useimpact%d" % index,), 0))
            threshold = self._parm_value(solver, ("constraint_impactthreshold%d" % index,), None)
            if use_impact and isinstance(threshold, (int, float)) and threshold <= 0:
                self.add_issue(
                    "RBD_NONPOSITIVE_IMPACT_THRESHOLD",
                    "warning",
                    "high",
                    "rbd",
                    path,
                    "Impact Break Thresholdが0以下です",
                    {"rule_index": index, "threshold": threshold, "group": group},
                    "ほぼすべての衝撃で即時破断しないか確認してください。",
                    ["glue"],
                )

    def _diagnose_apex_profiles(self) -> None:
        if not self._profile_enabled("apex"):
            return
        for node in self.nodes:
            if not (_is_apex_node(node) or _is_kinefx_node(node)):
                continue
            if self.scan_level == "fast":
                self._diagnose_apex_static(node)
                continue
            snapshot = self._main_snapshot_for_node(node) or self._snapshot_node_output(node, 0)
            if snapshot is None:
                continue
            self._diagnose_apex_static(node)
            self._diagnose_packed_character(node, snapshot)
            self._diagnose_kinefx_skeleton(node, snapshot)
            if _is_apex_node(node):
                self._diagnose_apex_graph(node, snapshot)
            self._diagnose_kinefx_special_nodes(node)

    def _diagnose_apex_static(self, node: Any) -> None:
        path = _node_path(node)
        text = _node_type_text(node)
        if "apex::invokegraph" in text or "apex invoke graph" in text:
            graph_path = self._parm_string(node, ("graph", "graphpath", "rigpath", "graphname"), "")
            if not graph_path:
                self.add_issue(
                    "APEX_INVOKE_GRAPH_TARGET_EMPTY",
                    "warning",
                    "medium",
                    "apex",
                    path,
                    "Invoke Graphの対象Graph指定が空の可能性があります",
                    suggestion="Graph入力またはPacked Folder内のGraphパスを確認してください。",
                    symptoms=["apex_graph"],
                )
        if "sceneanimate" in text and not (_safe(lambda: node.inputs(), ()) or ()):
            self.add_issue(
                "APEX_SCENE_ANIMATE_INPUT_MISSING",
                "error",
                "high",
                "apex",
                path,
                "APEX Scene AnimateへScene入力がありません",
                symptoms=["apex_graph"],
            )

    def _diagnose_apex_graph(self, node: Any, snapshot: GeometrySnapshot) -> None:
        if apex is None:
            self.scan_notes.append("APEX Python module is unavailable; graph-level checks were skipped.")
            return
        path = _node_path(node)
        geometry = None
        try:
            geometry = node.geometry(snapshot.output_index)
            graph = apex.Graph()
            loaded = bool(graph.loadFromGeometry(geometry, False))
        except Exception as exc:
            self.add_issue(
                "APEX_GRAPH_LOAD_EXCEPTION",
                "warning",
                "high",
                "apex",
                path,
                "APEX Graph APIでGeometryを読み込めませんでした",
                {"error": "%s: %s" % (exc.__class__.__name__, exc)},
                "Graph出力ではないAPEX SOPなら問題ありません。Graph SOPなら入力Geometryを確認してください。",
                ["apex_graph"],
            )
            return
        if not loaded:
            return

        try:
            node_ids = list(graph.allNodes())
            port_ids = list(graph.allPorts())
        except Exception as exc:
            self.add_issue(
                "APEX_GRAPH_ENUMERATION_FAILED",
                "error",
                "high",
                "apex",
                path,
                "APEX GraphのNode/Portを列挙できません",
                {"error": str(exc)},
                symptoms=["apex_graph"],
            )
            return

        graph_errors = list(_safe(lambda: graph.errors(), ()) or ())
        graph_warnings = list(_safe(lambda: graph.warnings(), ()) or ())
        for message in graph_errors:
            self.add_issue(
                "APEX_GRAPH_ERROR",
                "error",
                "high",
                "apex",
                path,
                "APEX Graphエラー: " + str(message),
                symptoms=["apex_graph"],
            )
        for message in graph_warnings:
            self.add_issue(
                "APEX_GRAPH_WARNING",
                "warning",
                "high",
                "apex",
                path,
                "APEX Graph警告: " + str(message),
                symptoms=["apex_graph"],
            )

        node_paths: Dict[str, int] = {}
        duplicate_paths: List[str] = []
        orphan_nodes: List[str] = []
        for node_id in node_ids:
            graph_node_path = str(_safe(lambda node_id=node_id: graph.nodePath(node_id), "") or "")
            graph_node_name = str(_safe(lambda node_id=node_id: graph.nodeName(node_id), "") or "")
            display = graph_node_path or graph_node_name or str(node_id)
            normalized = graph_node_path.casefold()
            if normalized:
                if normalized in node_paths:
                    duplicate_paths.append(graph_node_path)
                else:
                    node_paths[normalized] = node_id
            input_ports = list(_safe(lambda node_id=node_id: graph.getInputPorts(node_id), ()) or ())
            output_ports = list(_safe(lambda node_id=node_id: graph.getOutputPorts(node_id), ()) or ())
            connected = 0
            for port_id in input_ports + output_ports:
                connected += len(_safe(lambda port_id=port_id: graph.connectedPorts(port_id), ()) or ())
            if connected == 0 and input_ports + output_ports:
                lower = display.lower()
                if not any(token in lower for token in ("graphinput", "graphoutput", "constant", "parameter")):
                    orphan_nodes.append(display)

        if duplicate_paths:
            self.add_issue(
                "APEX_GRAPH_DUPLICATE_NODE_PATHS",
                "error",
                "high",
                "apex",
                path,
                "APEX Graph内に重複Node Pathがあります",
                {"count": len(duplicate_paths), "sample": duplicate_paths[:30]},
                "Merge Graph、Subnet変換、Node Rename処理を確認してください。",
                ["apex_graph"],
            )
        if orphan_nodes:
            self.add_issue(
                "APEX_GRAPH_ORPHAN_NODES",
                "notice",
                "medium",
                "apex",
                path,
                "APEX Graph内に未接続ノードがあります",
                {"count": len(orphan_nodes), "sample": orphan_nodes[:30]},
                "意図した予備ノードでなければ削除またはWire接続を確認してください。",
                ["apex_graph", "performance"],
            )

        graph_outputs = list(_safe(lambda: graph.outputPorts(), ()) or ())
        disconnected_outputs = []
        for port_id in graph_outputs:
            connected = list(_safe(lambda port_id=port_id: graph.connectedPorts(port_id), ()) or ())
            if not connected:
                disconnected_outputs.append(str(_safe(lambda port_id=port_id: graph.portPath(port_id), port_id)))
        if disconnected_outputs:
            self.add_issue(
                "APEX_GRAPH_OUTPUT_UNCONNECTED",
                "error",
                "high",
                "apex",
                path,
                "APEX Graph Outputに未接続Portがあります",
                {"count": len(disconnected_outputs), "ports": disconnected_outputs[:40]},
                "Graph Outputへ計算結果をWireしてください。",
                ["apex_graph"],
            )

        unresolved_ports = []
        for port_id in port_ids:
            type_name = str(_safe(lambda port_id=port_id: graph.portTypeName(port_id), "") or "")
            if not type_name or any(token in type_name.lower() for token in ("unknown", "unresolved")):
                unresolved_ports.append(
                    {
                        "path": str(_safe(lambda port_id=port_id: graph.portPath(port_id), port_id)),
                        "type": type_name,
                    }
                )
        if unresolved_ports:
            self.add_issue(
                "APEX_GRAPH_UNRESOLVED_PORT_TYPES",
                "warning",
                "high",
                "apex",
                path,
                "APEX Port型を解決できていません",
                {"count": len(unresolved_ports), "sample": unresolved_ports[:30]},
                "Wireの型、Variadic Port、Graph Inputの型指定を確認してください。",
                ["apex_graph"],
            )

        compile_errors: List[str] = []
        if self.scan_level == "deep":
            before_errors = set(str(item) for item in graph_errors)
            try:
                graph.compileProgram()
            except Exception as exc:
                self.add_issue(
                    "APEX_GRAPH_COMPILE_EXCEPTION",
                    "error",
                    "high",
                    "apex",
                    path,
                    "APEX Graphのコンパイルに失敗しました",
                    {"error": "%s: %s" % (exc.__class__.__name__, exc)},
                    "Port型、Graph Output、循環依存、欠けたCallbackを確認してください。",
                    ["apex_graph"],
                )
            after_errors = [str(item) for item in (_safe(lambda: graph.errors(), ()) or ())]
            new_errors = [item for item in after_errors if item not in before_errors]
            compile_errors = list(new_errors)
            if new_errors:
                self.add_issue(
                    "APEX_GRAPH_COMPILE_ERRORS",
                    "error",
                    "high",
                    "apex",
                    path,
                    "APEX Graphコンパイルでエラーが発生しました",
                    {"errors": new_errors[:50]},
                    symptoms=["apex_graph"],
                )

        apex_contract_ok = not (
            graph_errors
            or duplicate_paths
            or disconnected_outputs
            or unresolved_ports
            or compile_errors
        )
        self.add_check(
            "APEX_GRAPH_STRUCTURE",
            "pass" if apex_contract_ok else "fail",
            "apex",
            path,
            {
                "context": "apex_graph_geometry",
                "graph_node_count": len(node_ids),
                "graph_port_count": len(port_ids),
                "graph_output_count": len(graph_outputs),
                "graph_error_count": len(graph_errors),
                "duplicate_node_path_count": len(duplicate_paths),
                "unconnected_graph_output_count": len(disconnected_outputs),
                "unresolved_port_type_count": len(unresolved_ports),
                "compile_error_count": len(compile_errors),
                "compile_checked": self.scan_level == "deep",
            },
        )

        self.node_records.setdefault(path, {})["apex_graph_summary"] = {
            "nodes": len(node_ids),
            "ports": len(port_ids),
            "graph_outputs": len(graph_outputs),
            "errors": len(graph_errors),
            "warnings": len(graph_warnings),
            "orphan_nodes": len(orphan_nodes),
        }

    def _diagnose_packed_character(self, node: Any, snapshot: GeometrySnapshot) -> None:
        text = _node_type_text(node)
        path = _node_path(node)
        is_character_node = any(
            token in text
            for token in ("packcharacter", "characterpack", "sceneaddcharacter", "sceneanimate", "configurecharacter", "packfolder")
        )
        if not is_character_node and not snapshot.packed_paths:
            return
        if is_character_node and not snapshot.packed_paths:
            self.add_issue(
                "APEX_PACKED_CHARACTER_PATHS_MISSING",
                "warning",
                "high",
                "apex",
                path,
                "Packed Character/Folderパスが見つかりません",
                "Character Packの入力とPack Folder階層を確認してください。",
                ["apex_graph"],
            )
            return
        normalized: Dict[str, str] = {}
        collisions: List[Tuple[str, str]] = []
        for packed_path in snapshot.packed_paths:
            key = re.sub(r"/+", "/", packed_path.replace("\\", "/")).rstrip("/").casefold()
            if key in normalized and normalized[key] != packed_path:
                collisions.append((normalized[key], packed_path))
            normalized[key] = packed_path
        if collisions:
            self.add_issue(
                "APEX_PACKED_PATH_CASE_COLLISION",
                "error",
                "high",
                "apex",
                path,
                "大文字小文字またはSlashだけが異なるPacked Pathがあります",
                {"count": len(collisions), "sample": collisions[:20]},
                "Windows環境では同一視されるため、Pack Folder名を一意化してください。",
                ["apex_graph"],
            )
        if "packcharacter" in text or "characterpack" in text:
            has_character_root = any(".char" in item.lower() for item in snapshot.packed_paths)
            if not has_character_root:
                self.add_issue(
                    "APEX_CHARACTER_ROOT_FOLDER_MISSING",
                    "warning",
                    "medium",
                    "apex",
                    path,
                    "Packed Path内に.char Character Rootが見つかりません",
                    {"path_sample": snapshot.packed_paths[:30]},
                    "カスタム命名なら問題ありません。標準APEX Character構造ならPack設定を確認してください。",
                    ["apex_graph"],
                )

    def _diagnose_kinefx_skeleton(self, node: Any, snapshot: GeometrySnapshot) -> None:
        text = _node_type_text(node)
        point_name = snapshot.stat("point", "name")
        transform = snapshot.stat("point", "transform")
        looks_like_skeleton = _is_kinefx_node(node) and point_name is not None and bool(snapshot.skeleton_edges)
        if not looks_like_skeleton:
            return
        path = _node_path(node)
        if point_name is None:
            return
        if point_name.empty_count:
            self.add_issue(
                "KINEFX_EMPTY_JOINT_NAMES",
                "error",
                "high",
                "kinefx",
                path,
                "空のJoint nameがあります",
                {"count": point_name.empty_count},
                "Skeleton、Import、Rename処理を確認してください。",
                ["apex_graph"],
            )
        if point_name.duplicate_count:
            self.add_issue(
                "KINEFX_DUPLICATE_JOINT_NAMES",
                "error",
                "high",
                "kinefx",
                path,
                "重複Joint nameがあります",
                {"duplicate_count": point_name.duplicate_count, "sample": point_name.sample},
                "Retarget、Capture、APEX Control MappingではJoint nameを一意にしてください。",
                ["apex_graph", "capture"],
            )
        if transform is None and any(token in text for token in ("skeleton", "rigpose", "joint", "character")):
            self.add_issue(
                "KINEFX_TRANSFORM_ATTRIBUTE_MISSING",
                "error",
                "high",
                "kinefx",
                path,
                "Skeleton Pointにtransform属性がありません",
                "KineFX SkeletonのPoint transform Matrix3を保持してください。",
                ["apex_graph", "capture"],
            )
        elif transform is not None and transform.tuple_size not in (9, 16):
            self.add_issue(
                "KINEFX_TRANSFORM_WRONG_SIZE",
                "error",
                "high",
                "kinefx",
                path,
                "transform属性のTuple SizeがMatrixとして不正です",
                {"tuple_size": transform.tuple_size, "data_type": transform.data_type},
                "Attribute PromoteやWrangleでtransform型を壊していないか確認してください。",
                ["apex_graph"],
            )

        joint_count = snapshot.counts.get("points", 0)
        parent_counts = [0] * joint_count
        children: Dict[int, List[int]] = {index: [] for index in range(joint_count)}
        self_edges = 0
        for parent, child in snapshot.skeleton_edges:
            if parent == child:
                self_edges += 1
                continue
            if 0 <= parent < joint_count and 0 <= child < joint_count:
                parent_counts[child] += 1
                children.setdefault(parent, []).append(child)
        multiple_parents = [index for index, count in enumerate(parent_counts) if count > 1]
        if multiple_parents:
            names = point_name.values
            self.add_issue(
                "KINEFX_MULTIPLE_PARENTS",
                "error",
                "high",
                "kinefx",
                path,
                "複数の親を持つJointがあります",
                {
                    "count": len(multiple_parents),
                    "joint_sample": [names[index] if index < len(names) else index for index in multiple_parents[:30]],
                },
                "Parent Joints、Skeleton Merge、重複Primitiveを確認してください。",
                ["apex_graph", "capture"],
            )
        if self_edges:
            self.add_issue(
                "KINEFX_SELF_PARENT_JOINTS",
                "error",
                "high",
                "kinefx",
                path,
                "Joint自身を結ぶSkeleton Edgeがあります",
                {"count": self_edges},
                symptoms=["apex_graph"],
            )

        state = [0] * joint_count
        cycle_nodes: Set[int] = set()

        def visit(index: int, stack: List[int]) -> None:
            if state[index] == 1:
                if index in stack:
                    cycle_nodes.update(stack[stack.index(index):])
                return
            if state[index] == 2:
                return
            state[index] = 1
            stack.append(index)
            for child in children.get(index, []):
                visit(child, stack)
            stack.pop()
            state[index] = 2

        for index in range(joint_count):
            if state[index] == 0:
                visit(index, [])
        if cycle_nodes:
            names = point_name.values
            self.add_issue(
                "KINEFX_PARENT_CYCLE",
                "critical",
                "high",
                "kinefx",
                path,
                "Skeleton階層に親子循環があります",
                {
                    "count": len(cycle_nodes),
                    "joint_sample": [names[index] if index < len(names) else index for index in sorted(cycle_nodes)[:30]],
                },
                "Parent JointsまたはAPEX GraphのParent設定を修正してください。",
                ["apex_graph", "capture"],
            )
        isolated = [index for index in range(joint_count) if parent_counts[index] == 0 and not children.get(index)]
        if isolated and len(isolated) < joint_count:
            names = point_name.values
            self.add_issue(
                "KINEFX_ISOLATED_JOINTS",
                "notice",
                "medium",
                "kinefx",
                path,
                "階層へ接続されていないJointがあります",
                {
                    "count": len(isolated),
                    "joint_sample": [names[index] if index < len(names) else index for index in isolated[:30]],
                },
                "意図した補助JointでなければParent接続を確認してください。",
                ["apex_graph"],
            )
        transform_valid = transform is not None and transform.tuple_size in (9, 16)
        skeleton_ok = not (
            point_name.empty_count
            or point_name.duplicate_count
            or not transform_valid
            or multiple_parents
            or self_edges
            or cycle_nodes
        )
        self.add_check(
            "KINEFX_SKELETON_STRUCTURE",
            "pass" if skeleton_ok else "fail",
            "kinefx",
            path,
            {
                "context": "kinefx_point_skeleton",
                "joint_count": joint_count,
                "empty_joint_name_count": point_name.empty_count,
                "duplicate_joint_name_count": point_name.duplicate_count,
                "transform_present": transform is not None,
                "transform_tuple_size": transform.tuple_size if transform is not None else None,
                "multiple_parent_joint_count": len(multiple_parents),
                "self_parent_edge_count": self_edges,
                "cycle_joint_count": len(cycle_nodes),
                "isolated_joint_count": len(isolated),
            },
        )

    def _diagnose_kinefx_special_nodes(self, node: Any) -> None:
        text = _node_type_text(node)
        path = _node_path(node)
        if self.scan_level == "fast":
            return
        if "jointdeform" in text or "deform skeleton" in text:
            skin = self._snapshot_input(node, 0)
            skeleton = self._snapshot_input(node, 1)
            if skin is not None:
                capture_owner = skin.attribute_owner("boneCapture")
                capture_tables = [
                    name
                    for attrs in skin.attributes.values()
                    for name in attrs
                    if "capture" in name.lower()
                ]
                if capture_owner is None and not capture_tables:
                    self.add_issue(
                        "KINEFX_CAPTURE_ATTRIBUTE_MISSING",
                        "error",
                        "high",
                        "kinefx",
                        path,
                        "Joint Deform入力にCapture属性がありません",
                        {"skin_source": skin.node_path},
                        "Capture Proximity/Biharmonic/Paintの出力とboneCaptureを確認してください。",
                        ["capture"],
                    )
            if skeleton is not None:
                if skeleton.stat("point", "name") is None or skeleton.stat("point", "transform") is None:
                    self.add_issue(
                        "KINEFX_DEFORM_SKELETON_CONTRACT_MISSING",
                        "error",
                        "high",
                        "kinefx",
                        path,
                        "Joint DeformのSkeleton入力にnameまたはtransformがありません",
                        {"skeleton_source": skeleton.node_path},
                        symptoms=["capture"],
                    )

        if any(token in text for token in ("retarget", "mapcharacter", "fktransfer", "mappoints")):
            source = self._snapshot_input(node, 0)
            target = self._snapshot_input(node, 1)
            if source is not None and target is not None:
                source_names = source.stat("point", "name")
                target_names = target.stat("point", "name")
                if source_names is not None and target_names is not None:
                    left = {str(value) for value in source_names.values if str(value)}
                    right = {str(value) for value in target_names.values if str(value)}
                    overlap = left & right
                    denominator = max(1, min(len(left), len(right)))
                    ratio = len(overlap) / float(denominator)
                    if not overlap:
                        self.add_issue(
                            "KINEFX_MAPPING_NO_NAME_OVERLAP",
                            "warning",
                            "medium",
                            "kinefx",
                            path,
                            "2つのSkeleton間で一致するJoint nameがありません",
                            {"source_count": len(left), "target_count": len(right)},
                            "明示的Mappingを使う構成でなければJoint RenameとNamespaceを確認してください。",
                            ["apex_graph", "retarget"],
                        )
                    elif ratio < 0.25:
                        self.add_issue(
                            "KINEFX_MAPPING_LOW_NAME_OVERLAP",
                            "notice",
                            "medium",
                            "kinefx",
                            path,
                            "Skeleton間のJoint name一致率が低いです",
                            {"overlap": len(overlap), "ratio": ratio, "sample": sorted(overlap)[:20]},
                            "Mapping Attributeを使う場合は問題ありません。自動一致を期待するなら名前を確認してください。",
                            ["retarget"],
                        )

        if "motionclip" in text:
            snapshot = self._main_snapshot_for_node(node)
            if snapshot is not None:
                has_clip_info = any(
                    name.lower() == "clipinfo" or "clipinfo" in name.lower()
                    for attrs in snapshot.attributes.values()
                    for name in attrs
                )
                if not has_clip_info and "create" not in text:
                    self.add_issue(
                        "KINEFX_MOTIONCLIP_INFO_MISSING",
                        "notice",
                        "medium",
                        "kinefx",
                        path,
                        "MotionClip出力にclipinfoが見つかりません",
                        "MotionClip Create/Configure Clip Infoの接続を確認してください。",
                    )

    def _cache_active_load_path(self, node: Any) -> Tuple[str, str, Dict[str, Any]]:
        """Return the path actually used by the cache's current file mode."""
        file_method_parm = self._parm(node, "filemethod")
        sop_output_parm = self._parm(node, "sopoutput")
        if file_method_parm is not None and sop_output_parm is not None:
            file_method_value = _safe(lambda: file_method_parm.eval(), None)
            file_method_token = str(_safe(lambda: file_method_parm.evalAsString(), file_method_value) or file_method_value)
            path = str(_safe(lambda: sop_output_parm.evalAsString(), "") or "")
            return path, "sopoutput", {
                "file_method_value": file_method_value,
                "file_method_token": file_method_token,
                "file_method_interpreted_by_sopoutput_expression": True,
            }
        for parm_name in ("sopoutput", "file", "file1", "outputfile", "filepath", "cachefile"):
            parm = self._parm(node, parm_name)
            if parm is None:
                continue
            path = str(_safe(lambda parm=parm: parm.evalAsString(), "") or "")
            if path:
                return path, parm_name, {}
        return "", "", {}

    def _diagnose_cache_boundaries(self) -> None:
        for node in self.nodes:
            if not _is_cache_node(node):
                continue
            path = _node_path(node)
            load_from_disk = self._parm_value(
                node,
                ("loadfromdisk", "loadfromdisk0", "load", "reload"),
                None,
            )
            file_path, active_path_parameter, cache_mode = self._cache_active_load_path(node)
            if load_from_disk and file_path:
                expanded = str(_safe(lambda: hou.expandString(file_path), file_path))
                path_exists = os.path.exists(os.path.normpath(expanded))
                missing_frame_mode = self._parm_value(node, ("missingframe",), None)
                self.add_check(
                    "CACHE_ACTIVE_LOAD_TARGET",
                    "pass" if path_exists else "review",
                    "cache",
                    path,
                    {
                        "context": "active_load_target",
                        "load_from_disk": True,
                        "active_path_parameter": active_path_parameter,
                        "active_path": expanded,
                        "active_path_exists_at_scan_frame": path_exists,
                        "missing_frame_mode": missing_frame_mode,
                        **cache_mode,
                    },
                )
                if not FRAME_TOKEN_RE.search(expanded) and not path_exists:
                    self.add_issue(
                        "CACHE_LOAD_FILE_MISSING",
                        "error",
                        "high",
                        "cache",
                        path,
                        "Load from Diskが有効ですがCacheファイルがありません",
                        {
                            "path": expanded,
                            "active_path_parameter": active_path_parameter,
                            "missing_frame_mode": missing_frame_mode,
                            **cache_mode,
                        },
                        "Cacheを作成するか、Load from Diskとファイル名を確認してください。",
                        ["cache"],
                    )

            upstream_time_nodes = []
            visited: Set[str] = set()
            frontier = list(_safe(lambda node=node: node.inputs(), ()) or ())
            depth = 0
            while frontier and depth < 20 and len(visited) < 500:
                next_frontier = []
                for upstream in frontier:
                    upstream_path = _node_path(upstream)
                    if not upstream_path or upstream_path in visited:
                        continue
                    visited.add(upstream_path)
                    if upstream_path in self.time_dependent_nodes:
                        upstream_time_nodes.append(upstream_path)
                    next_frontier.extend(list(_safe(lambda upstream=upstream: upstream.inputs(), ()) or ()))
                frontier = next_frontier
                depth += 1

            frame_range_single = False
            first = self._parm_value(node, ("f1", "start", "startframe"), None)
            last = self._parm_value(node, ("f2", "end", "endframe"), None)
            if isinstance(first, (int, float)) and isinstance(last, (int, float)):
                frame_range_single = abs(float(first) - float(last)) < 1e-6
            if frame_range_single and upstream_time_nodes:
                self.add_issue(
                    "CACHE_SINGLE_FRAME_FREEZES_TIME_DEPENDENCY",
                    "warning",
                    "high",
                    "cache",
                    path,
                    "1フレームCacheより上流に時間依存ノードがあります",
                    {"upstream_time_dependent_count": len(upstream_time_nodes), "sample": upstream_time_nodes[:30]},
                    "active、v、w、Glue strengthなどの動的処理はUnpack後へ移してください。",
                    ["cache", "glue"],
                    upstream_time_nodes[:30],
                )

            if self.scan_level != "fast":
                before = self._snapshot_input(node, 0)
                after = self._main_snapshot_for_node(node) or self._snapshot_node_output(node, 0)
                if before is not None and after is not None:
                    self._compare_cache_contract(path, before, after)

    def _compare_cache_contract(
        self,
        cache_path: str,
        before: GeometrySnapshot,
        after: GeometrySnapshot,
    ) -> None:
        for name in ("name", "constraint_name", "strength", "active", "v", "w", "transform"):
            left = before.any_stat(name)
            right = after.any_stat(name)
            if left is not None and right is None:
                severity = "error" if name in ("name", "constraint_name", "transform") else "warning"
                self.add_issue(
                    "CACHE_ATTRIBUTE_DROPPED",
                    severity,
                    "high",
                    "cache",
                    cache_path,
                    "Cache境界で属性が消えました: " + name,
                    {"before": before.node_path, "after": after.node_path},
                    "Cache HDAが持ち越せる属性と、Unpack後の再作成処理を確認してください。",
                    ["cache", "frame_one_explosion", "apex_graph"],
                )
            elif left is not None and right is not None and name in ("name", "constraint_name"):
                if left.fingerprint != right.fingerprint:
                    self.add_issue(
                        "CACHE_IDENTITY_CHANGED",
                        "critical",
                        "high",
                        "cache",
                        cache_path,
                        "Cache境界で識別属性が変化しました: " + name,
                        {"before": left.to_dict(), "after": right.to_dict()},
                        "Cache前後で同じ最終nameを保持してください。",
                        ["cache", "frame_one_explosion"],
                    )

    def _diagnose_frame_differences(self) -> None:
        candidates = [node for node in self.nodes if _is_sop(node) and self._should_snapshot_node(node)]
        if len(candidates) > 30:
            candidates = candidates[:30]
            self.scan_notes.append("Frame comparison was limited to 30 important SOP nodes.")
        frames = sorted(set(float(frame) for frame in self.compare_frames))
        for node in candidates:
            snapshots = [self._snapshot_node_output(node, 0, frame=frame) for frame in frames]
            snapshots = [snapshot for snapshot in snapshots if snapshot is not None]
            if len(snapshots) < 2:
                continue
            base = snapshots[0]
            for snapshot in snapshots[1:]:
                if snapshot.counts != base.counts:
                    self.add_issue(
                        "FRAME_TOPOLOGY_CHANGED",
                        "notice",
                        "high",
                        "time",
                        _node_path(node),
                        "比較フレーム間でTopology数が変化しました",
                        {
                            "frame_a": base.frame,
                            "counts_a": base.counts,
                            "frame_b": snapshot.frame,
                            "counts_b": snapshot.counts,
                        },
                        "時間依存TopologyがCacheやSolver契約へ影響しないか確認してください。",
                        ["cache", "apex_graph"],
                    )
                left_name = self._name_stat(base)
                right_name = self._name_stat(snapshot)
                left_set = self._identity_set(left_name)
                right_set = self._identity_set(right_name)
                if left_set is not None and right_set is not None and left_set != right_set:
                    only_a = sorted(left_set - right_set)
                    only_b = sorted(right_set - left_set)
                    self.add_issue(
                        "FRAME_NAME_SET_CHANGED",
                        "warning",
                        "high",
                        "time",
                        _node_path(node),
                        "比較フレーム間でname集合差があります",
                        {
                            "frame_a": base.frame,
                            "frame_b": snapshot.frame,
                            "frame_a_unique_count": len(left_set),
                            "frame_b_unique_count": len(right_set),
                            "frame_a_only_count": len(only_a),
                            "frame_a_only_sample": only_a[:12],
                            "frame_b_only_count": len(only_b),
                            "frame_b_only_sample": only_b[:12],
                            "sets_measured_exactly": True,
                        },
                        "RBD/APEXの識別子が時間変化していないか確認してください。",
                        ["cache", "frame_one_explosion", "apex_graph"],
                    )


def _json_text(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True)


def _compact_llm_value(value: Any, depth: int = 0) -> Any:
    if depth > 5:
        return "<nested-data-omitted>"
    if isinstance(value, dict):
        result: Dict[str, Any] = {}
        for key, item in value.items():
            if key in ("fingerprint",):
                continue
            result[str(key)] = _compact_llm_value(item, depth + 1)
        return result
    if isinstance(value, (list, tuple)):
        items = list(value)
        compact = [_compact_llm_value(item, depth + 1) for item in items[:12]]
        if len(items) > 12:
            compact.append("<%d-more>" % (len(items) - 12))
        return compact
    if isinstance(value, str) and len(value) > 600:
        return value[:600] + "..."
    return value


def render_issue_markdown(issue: Dict[str, Any], compact: bool = False) -> List[str]:
    severity = issue.get("severity_ja") or issue.get("severity")
    confidence = issue.get("confidence", "")
    lines = ["### [%s / %s] %s" % (severity, confidence, issue.get("summary", "")), ""]
    if issue.get("node_path"):
        lines.append("- Node: `%s`" % issue["node_path"])
    lines.append("- Rule: `%s`" % issue.get("rule_id", ""))
    lines.append("- Profile: `%s`" % issue.get("profile", ""))
    evidence = issue.get("evidence") or {}
    if evidence:
        if compact:
            evidence_text = json.dumps(evidence, ensure_ascii=False, sort_keys=True)
            if len(evidence_text) > 1200:
                evidence_text = evidence_text[:1200] + "..."
            lines.append("- Evidence: `%s`" % evidence_text.replace("`", "'"))
        else:
            lines.extend(["", "Evidence:", "", "```json", _json_text(evidence), "```"])
    if issue.get("suggestion"):
        lines.extend(["", "Suggestion: %s" % issue["suggestion"]])
    lines.append("")
    return lines


def render_markdown(report: Dict[str, Any]) -> str:
    summary = report.get("summary", {})
    scene = report.get("scene", {})
    options = report.get("options", {})
    lines = [
        "# Houdini Network Preflight",
        "",
        "- Tool version: `%s`" % report.get("tool", {}).get("version", ""),
        "- HIP: `%s`" % scene.get("hip_file", ""),
        "- Houdini: `%s`" % scene.get("houdini_version", ""),
        "- Frame: `%s`" % scene.get("frame", ""),
        "- Profile: `%s`" % options.get("profile", ""),
        "- Scan: `%s`" % options.get("scan_level", ""),
        "- Nodes: `%s`" % summary.get("node_count", 0),
        "- Issues: `%s`" % summary.get("issue_count", 0),
        "",
        "## Severity Summary",
        "",
    ]
    for severity in ("critical", "error", "warning", "notice", "info"):
        count = summary.get("severity_counts", {}).get(severity, 0)
        lines.append("- %s: %s" % (SEVERITY_LABEL_JA.get(severity, severity), count))
    checks = report.get("checks", [])
    lines.extend(["", "## Contract Checks", ""])
    if not checks:
        lines.append("No explicit contract checks were recorded.")
    for check in checks:
        lines.append(
            "- [%s] `%s` — `%s`"
            % (str(check.get("status", "")).upper(), check.get("check_id", ""), check.get("node_path", ""))
        )
        if check.get("evidence"):
            lines.append("  - Evidence: `%s`" % json.dumps(_compact_llm_value(check["evidence"]), ensure_ascii=False, sort_keys=True).replace("`", "'"))
    lines.extend(["", "## Findings", ""])
    issues = report.get("issues", [])
    if not issues:
        lines.append("No findings.")
    for issue in issues:
        lines.extend(render_issue_markdown(issue, compact=False))
    if report.get("notes"):
        lines.extend(["", "## Scan Notes", ""])
        lines.extend("- " + str(note) for note in report["notes"])
    return "\n".join(lines).rstrip() + "\n"


LLM_REVIEW_CHECK_SYMPTOMS = {
    "RBD_ACTIVE_STATE_AT_SCAN_FRAME": {"rbd_general", "frame_one_explosion", "no_motion"},
    "RBD_AT_FRAME_BREAK_SCHEDULE": {"glue", "clock_driven_break"},
    "RBD_COLLIDER_MOTION_INPUT_EVIDENCE": {"tunneling", "collision_offset", "violent_fragments"},
    "RBD_CONFIGURE_ACTIVE_BOUNDS_COVERAGE": {"rbd_general", "no_motion"},
    "RBD_CONSTRAINT_GRAPH_TOPOLOGY": {"rbd_general", "glue"},
    "RBD_GLUE_NUMERIC_DISTRIBUTION": {"glue", "localized_impact"},
    "RBD_IMPACT_BREAK_RULE_SCOPE": {"glue", "localized_impact"},
    "RBD_SIM_RESPONSE_SAMPLE": {"glue", "localized_impact", "violent_fragments"},
    "CACHE_ACTIVE_LOAD_TARGET": {"cache", "frame_one_explosion"},
}


# These records are useful measurements in a complete report, but do not state
# a violated contract.  Auto briefs omit them to reduce anchoring in small LLMs.
LLM_AUTO_SUPPRESSED_REVIEW_CHECKS = {
    "RBD_ACTIVE_STATE_AT_SCAN_FRAME",
    "RBD_AT_FRAME_BREAK_SCHEDULE",
    "RBD_COLLIDER_MOTION_INPUT_EVIDENCE",
    "RBD_CONFIGURE_ACTIVE_BOUNDS_COVERAGE",
    "RBD_CONSTRAINT_GRAPH_TOPOLOGY",
    "RBD_GLUE_NUMERIC_DISTRIBUTION",
}


def _select_llm_checks(
    checks: Sequence[Dict[str, Any]],
    limit: int = 20,
    symptom: str = "auto",
) -> List[Dict[str, Any]]:
    check_order = {"fail": 0, "review": 1, "pass": 2, "not_checked": 3}
    ordered = sorted(
        checks,
        key=lambda item: (
            check_order.get(str(item.get("status", "")), 9),
            item.get("check_id", ""),
            item.get("node_path", ""),
        ),
    )
    selected: List[Dict[str, Any]] = []
    seen_ids: Set[str] = set()
    # Preserve variety before repeated checks from several RBD contract nodes.
    for check in ordered:
        check_id = str(check.get("check_id", ""))
        status = str(check.get("status", ""))
        if symptom == "auto" and check_id in LLM_AUTO_SUPPRESSED_REVIEW_CHECKS:
            continue
        if symptom != "auto" and status in ("review", "not_checked"):
            relevant_symptoms = LLM_REVIEW_CHECK_SYMPTOMS.get(check_id, set())
            if symptom not in relevant_symptoms:
                continue
        if check_id in seen_ids:
            continue
        selected.append(check)
        seen_ids.add(check_id)
        if len(selected) >= limit:
            return selected
    return selected


def _llm_issue_matches_symptom(issue: Dict[str, Any], symptom: str) -> bool:
    if symptom == "auto":
        return str(issue.get("severity", "")) != "info"
    if str(issue.get("llm_state", "review")) == "fail":
        return True
    if symptom in (issue.get("symptoms") or []):
        return True
    return bool(
        issue.get("severity") in ("critical", "error")
        and issue.get("confidence") == "high"
    )


def _compact_numeric_measurement(value: Any) -> Any:
    if not isinstance(value, dict):
        return value
    keep = (
        "present", "count", "numeric_count", "minimum", "median", "maximum",
        "negative_count", "zero_count", "positive_count", "unique_value_sample",
        "negative_value_role", "negative_values_excluded_from_finite_strength_range",
        "finite_strength_count", "finite_strength_minimum", "finite_strength_median",
        "finite_strength_maximum", "minimum_to_maximum_is_not_a_strength_spread_when_negative_values_exist",
    )
    return {key: value[key] for key in keep if key in value}


def _llm_check_evidence(check: Dict[str, Any]) -> Dict[str, Any]:
    evidence = dict(check.get("evidence") or {})
    check_id = str(check.get("check_id", ""))
    if check_id == "RBD_CONSTRAINT_GRAPH_TOPOLOGY":
        return {
            key: evidence.get(key)
            for key in (
                "context", "constraint_source", "geometry_unique_name_count",
                "named_node_count", "line_count", "component_count", "largest_component_size",
                "self_link_count", "geometry_and_endpoint_sets_measured_exactly",
                "geometry_names_without_constraint_endpoint_count",
                "geometry_names_without_constraint_endpoint_sample",
                "single_component_required_by_contract",
                "multiple_components_can_be_intentional_islands",
                "unconstrained_geometry_can_be_intentional_projectile_or_frame",
                "causal_effect_not_established",
            )
            if key in evidence
        }
    if check_id == "RBD_GLUE_NUMERIC_DISTRIBUTION":
        result = {
            key: evidence.get(key)
            for key in (
                "context", "constraint_source", "primitive_count", "static_distribution_only",
                "physical_cause_not_assigned", "requires_dynamic_response_measurement_for_behavior_claim",
            )
            if key in evidence
        }
        for key in ("strength", "propagate_rate", "propagationiterations", "impulse_halflife"):
            if key in evidence:
                result[key] = _compact_numeric_measurement(evidence[key])
        graph = evidence.get("graph") or {}
        result["graph"] = {
            key: graph.get(key)
            for key in ("named_node_count", "line_count", "component_count", "largest_component_size")
            if key in graph
        }
        return result
    if check_id == "RBD_IMPACT_BREAK_RULE_SCOPE":
        result = {
            key: evidence.get(key)
            for key in (
                "context", "rule_index", "constraint_names", "group_expression", "group_resolved",
                "group_resolver", "impact_threshold", "total_glue_primitive_count",
                "selected_glue_primitive_count", "outside_glue_primitive_count", "selected_glue_ratio",
            )
            if key in evidence
        }
        for side in ("selected", "outside"):
            source = evidence.get(side) or {}
            compact_side: Dict[str, Any] = {"primitive_count": source.get("primitive_count")}
            for key in ("strength", "propagate_rate", "propagationiterations"):
                if key in source:
                    compact_side[key] = _compact_numeric_measurement(source[key])
            graph = source.get("graph") or {}
            compact_side["graph"] = {
                key: graph.get(key)
                for key in ("named_node_count", "line_count", "component_count", "largest_component_size")
                if key in graph
            }
            result[side] = compact_side
        return result
    if check_id == "RBD_SIM_RESPONSE_SAMPLE":
        compact_samples = []
        for sample in evidence.get("samples") or []:
            compact_sample = {
                key: sample.get(key)
                for key in (
                    "frame", "measured", "piece_count", "active_piece_count",
                    "moving_piece_count_speed_gt_0_01", "moving_piece_count_speed_gt_0_1",
                    "maximum_speed", "active_speed_p50", "active_speed_p90", "active_speed_p99",
                    "moving_fraction_of_active", "velocity_x_positive_count_speed_gt_0_01",
                    "velocity_x_negative_count_speed_gt_0_01", "moving_name_sample", "constraint_primitive_count",
                    "constraint_count_change_from_first_sample", "error",
                    "collider_explicit_v_present", "collider_explicit_v_nonzero_count",
                    "collider_explicit_v_maximum", "collider_position_motion_from_previous_sample",
                    "collider_speedmax_attribute_minimum", "collider_speedmax_attribute_maximum",
                    "piece_velocity_alignment_to_fastest_collider_point",
                )
                if key in sample
            }
            if "constraint_strength" in sample:
                compact_sample["constraint_strength"] = _compact_numeric_measurement(sample["constraint_strength"])
            graph = sample.get("constraint_graph") or {}
            compact_sample["constraint_graph"] = {
                key: graph.get(key)
                for key in ("component_count", "largest_component_size", "named_node_count")
                if key in graph
            }
            compact_samples.append(compact_sample)
        return {
            "context": evidence.get("context"),
            "frames_requested": evidence.get("frames_requested"),
            "simulation_was_cooked": evidence.get("simulation_was_cooked"),
            "samples": compact_samples,
        }
    return evidence


def _aggregate_llm_issues(issues: Sequence[Dict[str, Any]], limit: int) -> List[Dict[str, Any]]:
    grouped: Dict[Tuple[str, str, str, str], List[Dict[str, Any]]] = {}
    order: List[Tuple[str, str, str, str]] = []
    for issue in issues:
        evidence_key = json.dumps(_compact_llm_value(issue.get("evidence") or {}), ensure_ascii=False, sort_keys=True)
        key = (
            str(issue.get("rule_id", "")),
            str(issue.get("severity", "")),
            str(issue.get("confidence", "")),
            evidence_key,
        )
        if key not in grouped:
            grouped[key] = []
            order.append(key)
        grouped[key].append(issue)

    result: List[Dict[str, Any]] = []
    for key in order:
        members = grouped[key]
        record = dict(members[0])
        if len(members) > 1:
            nodes = []
            for member in members:
                node_path = str(member.get("node_path", "") or "")
                if node_path and node_path not in nodes:
                    nodes.append(node_path)
            evidence = dict(record.get("evidence") or {})
            evidence["same_observation_occurrence_count"] = len(members)
            evidence["node_sample"] = nodes[:12]
            record["evidence"] = evidence
            record["related_nodes"] = nodes[1:12]
        result.append(record)
        if len(result) >= max(1, limit):
            break
    return result


def render_llm_brief(report: Dict[str, Any], limit: int = 20) -> str:
    summary = report.get("summary", {})
    scene = report.get("scene", {})
    options = report.get("options", {})
    symptom = str(options.get("symptom", "auto") or "auto")
    all_issues = list(report.get("issues", []))
    scoped_issues = [issue for issue in all_issues if _llm_issue_matches_symptom(issue, symptom)]
    issues = _aggregate_llm_issues(scoped_issues, max(1, limit))
    all_checks = list(report.get("checks", []))
    checks = _select_llm_checks(all_checks, 20, symptom=symptom)
    dynamic_response_measured = any(
        str(check.get("check_id", "")) == "RBD_SIM_RESPONSE_SAMPLE"
        and bool((check.get("evidence") or {}).get("simulation_was_cooked"))
        for check in all_checks
    )
    lines = [
        "# Houdini Preflight Evidence Packet",
        "",
        "## Instructions for the receiving LLM",
        "",
        "- `evidence`と`observed`だけを測定事実として扱う。",
        "- `tool_label`と`next_check`はヒューリスティックであり、原因や不具合の確定ではない。",
        "- `PASS`は記載された契約だけの合格、`FAIL`は明示契約違反、`REVIEW`は未確定候補、`NOT_CHECKED`は証拠不足を表す。",
        "- 要素数・Class・分布の入出力差だけから、属性消失・破損・因果関係を推定しない。identity集合差や契約FAILを優先する。",
        "- 数値分布・Group被覆率・Graph成分数は測定値であり、それ単独では物理挙動の原因を確定しない。",
        "- 静的Glue分布は意図した島構造でも現れる。見た目の硬さ・波及不足はCompare Framesの動的応答測定を優先する。",
        "- `確認済み`に因果的な「影響」を書かない。因果は明示的な複数フレーム応答測定がなければ`候補`に置く。",
        "- Glue strength=-1は破断不能Sentinelであり、有限値との大小差として扱わない。有限strengthの絶対的な強弱はScale・Mass・Impactとの比較なしに断定しない。",
        "- 走査フレームのstrength=-1だけでは将来フレームのロックを確定しない。At Frame・上流更新・Solver内削除後のConstraint数を測定する。",
        "- 1フレームのactive=0、補助identity空値、motion flag不在、未来のAt Frameだけから、未Activation・ID破損・静止Collider・現在のGlue維持を推定しない。",
        "- Dynamic solver response measured=falseなら、全体飛散・逆向き速度・無動作など時間応答の有無をこのPacketから判断しない。",
        "- 2点の開いたPolylineはConstraint/Curveとして扱う。面積0を縮退Surfaceと解釈しない。",
        "- ノード名・HIP名・コメントは文脈メタデータであり、測定事実ではない。",
        "- 症状指定時、このPacketは無関係なREVIEWを省略する。省略分は完全JSONレポートに残る。",
        "- 最終回答を `確認済み / 候補 / 不明` に分け、証拠のない断定をしない。",
        "",
        "## Scan Context",
        "",
        "- HIP: `%s`" % scene.get("hip_file", ""),
        "- Frame: `%s`" % scene.get("frame", ""),
        "- Profile / scan: `%s / %s`" % (options.get("profile", ""), options.get("scan_level", "")),
        "- Scope node count: %s" % summary.get("node_count", 0),
        "- Contract checks: %s (packet representatives: %s)" % (summary.get("check_count", len(all_checks)), len(checks)),
        "- Review records: %s" % summary.get("issue_count", 0),
        "- Symptom-focused review records shown: %s / %s" % (len(issues), len(all_issues)),
        "- Dynamic solver response measured: %s" % ("true" if dynamic_response_measured else "false"),
        "",
        "## Contract Checks",
        "",
    ]
    if not checks:
        lines.append("- status=NOT_CHECKED check_id=NO_EXPLICIT_CONTRACT_CHECKS")
    for check in checks:
        evidence = json.dumps(
            _compact_llm_value(_llm_check_evidence(check)),
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        lines.append(
            "- status=%s check_id=%s node=`%s` evidence=`%s`"
            % (
                str(check.get("status", "not_checked")).upper(),
                check.get("check_id", ""),
                check.get("node_path", ""),
                evidence.replace("`", "'"),
            )
        )
    lines.extend(["", "## Review Records (not conclusions)", ""])
    if not issues:
        lines.append("- No review records. This is not proof that the network is correct.")
    for index, issue in enumerate(issues, 1):
        lines.append("### R%02d" % index)
        lines.append("")
        lines.append("- state: `%s`" % str(issue.get("llm_state", "review")).upper())
        lines.append("- priority: `%s`" % issue.get("severity", ""))
        lines.append("- confidence: `%s`" % issue.get("confidence", ""))
        lines.append("- rule_id: `%s`" % issue.get("rule_id", ""))
        lines.append("- node: `%s`" % issue.get("node_path", ""))
        lines.append("- tool_label: `%s`" % str(issue.get("summary", "")).replace("`", "'"))
        evidence = issue.get("evidence") or {}
        if evidence:
            text = json.dumps(
                _compact_llm_value(evidence),
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            )
            lines.append("- observed: `%s`" % text.replace("`", "'"))
        if issue.get("suggestion"):
            lines.append("- next_check: %s" % issue["suggestion"])
        lines.append("")
    node_records = {record.get("path"): record for record in report.get("nodes", [])}
    relevant_paths = []
    for issue in issues:
        path = issue.get("node_path")
        if path and path not in relevant_paths:
            relevant_paths.append(path)
        for related in issue.get("related_nodes", []) or []:
            if related and related not in relevant_paths:
                relevant_paths.append(related)
    if relevant_paths:
        lines.extend(["", "## Relevant Graph Slice", ""])
        for path in relevant_paths[:12]:
            record = node_records.get(path)
            if record is None:
                lines.append("- `%s`" % path)
                continue
            inputs = [
                "%s[out%s] -> in%s" % (
                    item.get("source_node", ""),
                    item.get("source_output", 0),
                    item.get("input_index", 0),
                )
                for item in record.get("inputs", [])
            ]
            lines.append("- `%s` (%s)" % (path, record.get("type", "")))
            if inputs:
                lines.append("  - Inputs: " + "; ".join(inputs[:8]))
            outputs = record.get("outputs", [])
            if outputs:
                lines.append("  - Outputs: " + "; ".join(outputs[:8]))
    lines.extend(["", "## Requested judgement format", "", "1. 確認済み: PASS/FAILとobservedで直接支持される測定状態のみ。因果的な影響を書かない", "2. 候補: REVIEWから考えられる因果候補。反証候補も併記", "3. 不明: このpacketだけでは決められない内容", "4. 次に確認するノードと属性を最大5件"])
    return "\n".join(lines).rstrip() + "\n"


def analyze_selected(
    scope: str = "selected",
    profile: str = "auto",
    scan_level: str = "standard",
    symptom: str = "auto",
    compare_frames: Optional[Sequence[float]] = None,
) -> Dict[str, Any]:
    nodes = resolve_scope(scope)
    analyzer = HoudiniNetworkAnalyzer(
        nodes,
        profile=profile,
        scan_level=scan_level,
        symptom=symptom,
        compare_frames=compare_frames,
    )
    return analyzer.analyze()


def shelf_code(tool_path: Optional[str] = None) -> str:
    path = os.path.abspath(tool_path or __file__)
    return (
        '"""Launch Houdini Network Preflight inside Houdini."""\n\n'
        "from __future__ import annotations\n\n"
        "import runpy\n\n"
        "tool = runpy.run_path(r%r)\n" % path
        + 'tool["show_preflight_ui"]()\n'
    )


def save_report(report: Dict[str, Any], path: str) -> str:
    normalized = os.path.abspath(os.path.expanduser(path))
    parent = os.path.dirname(normalized)
    if parent and not os.path.isdir(parent):
        os.makedirs(parent)
    if normalized.lower().endswith(".json"):
        text = _json_text(report) + "\n"
    elif normalized.lower().endswith(".brief.md"):
        text = render_llm_brief(report)
    else:
        text = render_markdown(report)
    with open(normalized, "w", encoding="utf-8", newline="\n") as stream:
        stream.write(text)
    return normalized


def _import_qt() -> Tuple[Any, Any]:
    try:
        from PySide6 import QtCore, QtWidgets  # type: ignore

        return QtCore, QtWidgets
    except ImportError:
        from PySide2 import QtCore, QtWidgets  # type: ignore

        return QtCore, QtWidgets


def _qt_enum(container: Any, old_name: str, enum_name: str, member_name: str) -> Any:
    direct = getattr(container, old_name, None)
    if direct is not None:
        return direct
    enum = getattr(container, enum_name, None)
    return getattr(enum, member_name, None) if enum is not None else None


def _message_box_value(message_box: Any, old_name: str, member_name: str) -> Any:
    direct = getattr(message_box, old_name, None)
    if direct is not None:
        return direct
    standard_button = getattr(message_box, "StandardButton", None)
    return getattr(standard_button, member_name, None) if standard_button is not None else None


def _combo_value(combo: Any) -> str:
    data = combo.currentData()
    return str(data if data is not None else combo.currentText())


def _parse_compare_frames(text: str) -> List[float]:
    values = []
    for token in re.split(r"[,;\s]+", text.strip()):
        if not token:
            continue
        values.append(float(token))
    return values[:6]


class HoudiniPreflightDialog:
    def __init__(self, parent: Any = None) -> None:
        self.QtCore, self.QtWidgets = _import_qt()
        self.dialog = self.QtWidgets.QDialog(parent)
        self.dialog.setWindowTitle("%s %s" % (TOOL_NAME, VERSION))
        self.dialog.resize(1180, 760)
        self.report: Optional[Dict[str, Any]] = None
        self._build_ui()

    def _build_ui(self) -> None:
        QtCore, QtWidgets = self.QtCore, self.QtWidgets
        layout = QtWidgets.QVBoxLayout(self.dialog)

        intro = QtWidgets.QLabel(
            "ドラッグ選択したノードを、ルールベースで事前解析します。"
            "RBDはGeometry/Constraint/Proxy、APEX/KineFXはGraph/Port/Joint/Transform/Captureを重点検査します。"
            "出力ではPASS/FAIL/REVIEWと実測値を分離します。"
        )
        intro.setWordWrap(True)
        layout.addWidget(intro)

        options = QtWidgets.QGroupBox("解析設定")
        form = QtWidgets.QGridLayout(options)

        self.scope_combo = QtWidgets.QComboBox()
        for label, value in (
            ("選択ノードのみ", "selected"),
            ("選択 + 前後1ノード", "selected_plus_one"),
            ("選択 + 前後2ノード", "selected_plus_two"),
            ("同じネットワーク全体", "network"),
        ):
            self.scope_combo.addItem(label, value)
        self.scope_combo.setCurrentIndex(1)

        self.profile_combo = QtWidgets.QComboBox()
        for label, value in (
            ("自動: RBD + APEX + General", "auto"),
            ("RBD破壊", "rbd"),
            ("APEX / KineFX", "apex"),
            ("General SOP", "general"),
        ):
            self.profile_combo.addItem(label, value)

        self.scan_combo = QtWidgets.QComboBox()
        for label, value in (
            ("Fast: 原則Cookなし", "fast"),
            ("Standard: 重要SOPをCook", "standard"),
            ("Deep: Mesh/APEX Compile/Frame比較", "deep"),
        ):
            self.scan_combo.addItem(label, value)
        self.scan_combo.setCurrentIndex(1)

        self.symptom_combo = QtWidgets.QComboBox()
        for label, value in (
            ("症状指定なし", "auto"),
            ("全く動かない", "no_motion"),
            ("開始直後に爆散", "frame_one_explosion"),
            ("高速物体がすり抜ける", "tunneling"),
            ("滑りすぎる", "sliding"),
            ("Glue / Clusterがおかしい", "glue"),
            ("衝撃が周囲へ伝わらない", "localized_impact"),
            ("破片が激しく飛びすぎる", "violent_fragments"),
            ("Cache後に挙動が変わる", "cache"),
            ("処理が重い", "performance"),
            ("APEX Graph / Rigがおかしい", "apex_graph"),
            ("Capture / Deformがおかしい", "capture"),
            ("Retargetがおかしい", "retarget"),
        ):
            self.symptom_combo.addItem(label, value)

        self.frames_edit = QtWidgets.QLineEdit()
        self.frames_edit.setPlaceholderText("Deep比較フレーム 例: 1, 42, 75（最大6）")
        self.frames_edit.setEnabled(False)
        self.scan_combo.currentIndexChanged.connect(self._update_frame_enabled)

        form.addWidget(QtWidgets.QLabel("範囲"), 0, 0)
        form.addWidget(self.scope_combo, 0, 1)
        form.addWidget(QtWidgets.QLabel("Profile"), 0, 2)
        form.addWidget(self.profile_combo, 0, 3)
        form.addWidget(QtWidgets.QLabel("解析レベル"), 1, 0)
        form.addWidget(self.scan_combo, 1, 1)
        form.addWidget(QtWidgets.QLabel("症状"), 1, 2)
        form.addWidget(self.symptom_combo, 1, 3)
        form.addWidget(QtWidgets.QLabel("Frame比較"), 2, 0)
        form.addWidget(self.frames_edit, 2, 1, 1, 3)
        form.setColumnStretch(1, 1)
        form.setColumnStretch(3, 1)
        layout.addWidget(options)

        action_row = QtWidgets.QHBoxLayout()
        self.analyze_button = QtWidgets.QPushButton("選択範囲を解析")
        self.analyze_button.clicked.connect(self._analyze)
        self.copy_button = QtWidgets.QPushButton("LLM向けEvidence Packetをコピー")
        self.copy_button.clicked.connect(self._copy_brief)
        self.copy_button.setEnabled(False)
        self.save_button = QtWidgets.QPushButton("レポート保存...")
        self.save_button.clicked.connect(self._save_report)
        self.save_button.setEnabled(False)
        self.select_button = QtWidgets.QPushButton("問題ノードを表示")
        self.select_button.clicked.connect(self._focus_selected_issue)
        self.select_button.setEnabled(False)
        self.shelf_button = QtWidgets.QPushButton("Shelf起動コードをコピー")
        self.shelf_button.clicked.connect(self._copy_shelf_code)
        action_row.addWidget(self.analyze_button)
        action_row.addWidget(self.copy_button)
        action_row.addWidget(self.save_button)
        action_row.addWidget(self.select_button)
        action_row.addWidget(self.shelf_button)
        action_row.addStretch(1)
        layout.addLayout(action_row)

        self.progress = QtWidgets.QProgressBar()
        self.progress.setRange(0, 1)
        self.progress.setValue(0)
        self.status = QtWidgets.QLabel("")
        self.status.setWordWrap(True)
        layout.addWidget(self.progress)
        layout.addWidget(self.status)

        splitter = QtWidgets.QSplitter()
        horizontal = _qt_enum(QtCore.Qt, "Horizontal", "Orientation", "Horizontal")
        if horizontal is not None:
            splitter.setOrientation(horizontal)

        self.tree = QtWidgets.QTreeWidget()
        self.tree.setHeaderLabels(["優先度", "確度", "Profile", "Node", "観測ラベル"])
        self.tree.setAlternatingRowColors(True)
        self.tree.itemSelectionChanged.connect(self._show_issue_details)
        self.tree.itemDoubleClicked.connect(lambda *_args: self._focus_selected_issue())
        self.tree.setColumnWidth(0, 65)
        self.tree.setColumnWidth(1, 60)
        self.tree.setColumnWidth(2, 80)
        self.tree.setColumnWidth(3, 280)

        self.details = QtWidgets.QTextBrowser()
        self.details.setOpenExternalLinks(False)
        splitter.addWidget(self.tree)
        splitter.addWidget(self.details)
        splitter.setSizes([700, 480])
        layout.addWidget(splitter, 1)

        close_row = QtWidgets.QHBoxLayout()
        close_row.addStretch(1)
        close_button = QtWidgets.QPushButton("閉じる")
        close_button.clicked.connect(self.dialog.close)
        close_row.addWidget(close_button)
        layout.addLayout(close_row)

    def _update_frame_enabled(self) -> None:
        self.frames_edit.setEnabled(_combo_value(self.scan_combo) == "deep")

    def _confirm_cook(self, scan_level: str) -> bool:
        if scan_level == "fast":
            return True
        QtWidgets = self.QtWidgets
        yes = _message_box_value(QtWidgets.QMessageBox, "Yes", "Yes")
        no = _message_box_value(QtWidgets.QMessageBox, "No", "No")
        text = (
            "Standard/Deep解析は、属性・Group・RBD/APEX契約を確認するため選択範囲のSOPをCookする場合があります。\n"
            "Solverや重いFractureを含む場合は時間がかかります。続行しますか？"
        )
        result = QtWidgets.QMessageBox.question(
            self.dialog,
            TOOL_NAME,
            text,
            yes | no,
            no,
        )
        return result == yes

    def _progress_update(self, text: str, index: int, total: int) -> None:
        self.progress.setRange(0, max(1, total))
        self.progress.setValue(index)
        self.status.setText(text)
        self.QtWidgets.QApplication.processEvents()

    def _analyze(self) -> None:
        scan_level = _combo_value(self.scan_combo)
        if not self._confirm_cook(scan_level):
            return
        try:
            frames = _parse_compare_frames(self.frames_edit.text()) if scan_level == "deep" else []
        except ValueError:
            self.QtWidgets.QMessageBox.warning(self.dialog, TOOL_NAME, "Frame比較には数値をカンマ区切りで入力してください。")
            return
        nodes = resolve_scope(_combo_value(self.scope_combo))
        if not nodes:
            self.QtWidgets.QMessageBox.warning(self.dialog, TOOL_NAME, "Network Editorで解析対象ノードを選択してください。")
            return

        self.analyze_button.setEnabled(False)
        wait_cursor = _qt_enum(self.QtCore.Qt, "WaitCursor", "CursorShape", "WaitCursor")
        if wait_cursor is not None:
            self.QtWidgets.QApplication.setOverrideCursor(wait_cursor)
        try:
            analyzer = HoudiniNetworkAnalyzer(
                nodes,
                profile=_combo_value(self.profile_combo),
                scan_level=scan_level,
                symptom=_combo_value(self.symptom_combo),
                compare_frames=frames,
                progress=self._progress_update,
            )
            self.report = analyzer.analyze()
            self._populate_results()
        except Exception as exc:
            traceback.print_exc()
            self.QtWidgets.QMessageBox.critical(
                self.dialog,
                TOOL_NAME,
                "%s: %s" % (exc.__class__.__name__, exc),
            )
            self.status.setText("解析に失敗しました。Houdini ConsoleのTracebackを確認してください。")
        finally:
            if wait_cursor is not None:
                self.QtWidgets.QApplication.restoreOverrideCursor()
            self.analyze_button.setEnabled(True)

    def _populate_results(self) -> None:
        self.tree.clear()
        if not self.report:
            return
        role = _qt_enum(self.QtCore.Qt, "UserRole", "ItemDataRole", "UserRole")
        for index, issue in enumerate(self.report.get("issues", [])):
            item = self.QtWidgets.QTreeWidgetItem(
                [
                    str(issue.get("severity_ja", issue.get("severity", ""))),
                    str(issue.get("confidence", "")),
                    str(issue.get("profile", "")),
                    str(issue.get("node_path", "")),
                    str(issue.get("summary", "")),
                ]
            )
            if role is not None:
                item.setData(0, role, index)
            self.tree.addTopLevelItem(item)
        summary = self.report.get("summary", {})
        counts = summary.get("severity_counts", {})
        self.status.setText(
            "解析完了: %d nodes / %d findings — 重大 %d, エラー %d, 警告 %d, 注意 %d"
            % (
                summary.get("node_count", 0),
                summary.get("issue_count", 0),
                counts.get("critical", 0),
                counts.get("error", 0),
                counts.get("warning", 0),
                counts.get("notice", 0),
            )
        )
        self.progress.setRange(0, 1)
        self.progress.setValue(1)
        self.copy_button.setEnabled(True)
        self.save_button.setEnabled(True)
        self.select_button.setEnabled(bool(self.report.get("issues")))
        if self.tree.topLevelItemCount():
            self.tree.setCurrentItem(self.tree.topLevelItem(0))
        else:
            self.details.setPlainText(
                "ルールベースの異常候補は見つかりませんでした。\n"
                "これはネットワークが完全に正しいことを保証するものではありません。"
            )

    def _selected_issue(self) -> Optional[Dict[str, Any]]:
        if not self.report:
            return None
        item = self.tree.currentItem()
        if item is None:
            return None
        role = _qt_enum(self.QtCore.Qt, "UserRole", "ItemDataRole", "UserRole")
        index = item.data(0, role) if role is not None else None
        try:
            return self.report.get("issues", [])[int(index)]
        except Exception:
            return None

    def _show_issue_details(self) -> None:
        issue = self._selected_issue()
        if issue is None:
            self.details.clear()
            return
        lines = [
            "[%s / confidence %s]" % (issue.get("severity_ja", ""), issue.get("confidence", "")),
            issue.get("summary", ""),
            "",
            "Node: " + issue.get("node_path", ""),
            "Rule: " + issue.get("rule_id", ""),
            "Profile: " + issue.get("profile", ""),
        ]
        if issue.get("evidence"):
            lines.extend(["", "Evidence:", _json_text(issue["evidence"])])
        if issue.get("suggestion"):
            lines.extend(["", "Check:", issue["suggestion"]])
        if issue.get("related_nodes"):
            lines.extend(["", "Related nodes:"] + ["- " + path for path in issue["related_nodes"]])
        self.details.setPlainText("\n".join(lines))

    def _focus_selected_issue(self) -> None:
        issue = self._selected_issue()
        if issue is None or hou is None:
            return
        node = hou.node(issue.get("node_path", ""))
        if node is None:
            self.status.setText("問題ノードはすでに削除されています。")
            return
        _safe(lambda: node.setCurrent(True, clear_all_selected=True), None)
        network_editor = _safe(lambda: hou.ui.paneTabOfType(hou.paneTabType.NetworkEditor), None)
        if network_editor is not None:
            _safe(lambda: network_editor.setPwd(node.parent()), None)
            _safe(lambda: network_editor.setCurrentNode(node), None)
            _safe(lambda: network_editor.homeToSelection(), None)

    def _copy_brief(self) -> None:
        if not self.report:
            return
        text = render_llm_brief(self.report)
        self.QtWidgets.QApplication.clipboard().setText(text)
        self.status.setText("LLM向けEvidence PacketをClipboardへコピーしました。")

    def _copy_shelf_code(self) -> None:
        self.QtWidgets.QApplication.clipboard().setText(shelf_code())
        self.status.setText("Shelf Tool用の起動コードをClipboardへコピーしました。")

    def _save_report(self) -> None:
        if not self.report:
            return
        hip_path = str(self.report.get("scene", {}).get("hip_file", "") or "")
        base = os.path.splitext(hip_path)[0] if hip_path else os.path.join(os.path.expanduser("~"), "houdini_preflight")
        default_path = base + "_preflight.md"
        path, selected_filter = self.QtWidgets.QFileDialog.getSaveFileName(
            self.dialog,
            "Preflight Reportを保存",
            default_path,
            "Markdown (*.md);;JSON (*.json);;LLM Evidence Packet (*.brief.md)",
        )
        if not path:
            return
        if "JSON" in selected_filter and not path.lower().endswith(".json"):
            path += ".json"
        elif "Evidence" in selected_filter and not path.lower().endswith(".brief.md"):
            path += ".brief.md"
        elif not path.lower().endswith((".md", ".json")):
            path += ".md"
        try:
            saved = save_report(self.report, path)
        except Exception as exc:
            self.QtWidgets.QMessageBox.critical(self.dialog, TOOL_NAME, "%s: %s" % (exc.__class__.__name__, exc))
            return
        self.status.setText("保存しました: " + saved)

    def show(self) -> Any:
        self.dialog.show()
        self.dialog.raise_()
        self.dialog.activateWindow()
        return self.dialog


_PREFLIGHT_DIALOG: Optional[HoudiniPreflightDialog] = None


def _houdini_parent_window() -> Any:
    if hou is None:
        return None
    return _safe(lambda: hou.qt.mainWindow(), None)


def show_preflight_ui() -> Any:
    """Show the Houdini Network Preflight dialog."""
    global _PREFLIGHT_DIALOG
    if hou is None:
        raise RuntimeError("This UI must be launched inside Houdini")
    _PREFLIGHT_DIALOG = HoudiniPreflightDialog(_houdini_parent_window())
    return _PREFLIGHT_DIALOG.show()


def main() -> int:
    if hou is None:
        print("This tool must run inside Houdini or hython.")
        return 1
    report = analyze_selected(scope="selected_plus_one", profile="auto", scan_level="standard")
    print(render_llm_brief(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
