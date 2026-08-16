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
VERSION = "0.2.0"
SCHEMA = "houdini-network-preflight-v2"

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
    for prim in primitives[:20_000 if deep else 5_000]:
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

    degenerate_primitives = 0
    nonmanifold_edges = 0
    if deep:
        edge_counts: Dict[Tuple[int, int], int] = {}
        for prim in primitives[:250_000]:
            prim_points = _safe(lambda prim=prim: prim.points(), ()) or ()
            type_name = str(_safe(lambda prim=prim: prim.type().name(), "") or "").lower()
            if "poly" in type_name:
                if len(prim_points) < 3:
                    degenerate_primitives += 1
                area = _safe(lambda prim=prim: prim.intrinsicValue("measuredarea"), None)
                if isinstance(area, (int, float)) and abs(float(area)) < 1e-14:
                    degenerate_primitives += 1
                indices = [int(_safe(lambda point=point: point.number(), -1)) for point in prim_points]
                if len(indices) >= 2:
                    loop = indices + ([indices[0]] if len(indices) > 2 else [])
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
                    self.add_issue(
                        "HOUDINI_INTERNAL_HIGH_SIGNAL_MESSAGE",
                        "warning",
                        "high",
                        "performance" if "scatter" in normalized.lower() or "points" in normalized.lower() else "houdini",
                        _node_path(node),
                        "内部ノードに数値付きの高信号メッセージがあります",
                        {
                            "internal_node": _node_path(child),
                            "message": normalized,
                        },
                        "内部ノードの数値上限・生成数・Cook結果を確認してください。",
                        ["performance", "apex_graph"],
                        [_node_path(child)],
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
            standalone_control = bool(
                node is not None
                and "null" in _node_type_name(node).lower()
                and not any(item is not None for item in (_safe(lambda: node.inputs(), ()) or ()))
                and not (_safe(lambda: node.outputs(), ()) or ())
            )
            if standalone_control:
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
                "縮退Primitiveが検出されました",
                {"count": snapshot.degenerate_primitives},
                "PolyDoctor、Clean、Fuse許容値、二次フラクチャー設定を確認してください。",
                ["rbd_general", "performance"],
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
                    self.add_issue(
                        "IDENTITY_ATTRIBUTE_ALL_EMPTY_TRANSITION",
                        "warning",
                        "high",
                        "attribute",
                        _node_path(node),
                        "Identity属性が全空値になる境界を検出: " + down_stat.name,
                        {
                            "attribute": down_stat.name,
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
                        ["cache", "glue", "apex_graph"],
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

    def _diagnose_rbd_profiles(self) -> None:
        if not self._profile_enabled("rbd"):
            return
        for node in self.nodes:
            text = _node_type_text(node)
            if "rbdbulletsolver" in text or ("rbd bullet solver" in text):
                self._diagnose_rbd_solver(node)
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
            self.add_issue(
                "RBD_ALL_PIECES_INACTIVE",
                "warning",
                "medium",
                "rbd",
                owner_path,
                "現在のSolver入力では全ピースがactive=0です",
                {"frame": geometry.frame, "count": active.sampled},
                "後続の時間依存active更新がある場合はSolverのOverwrite Attributesも確認してください。",
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
                    "warning",
                    "high",
                    "rbd",
                    owner_path,
                    "friction値域が低摩擦ヒューリスティックに一致",
                    {
                        "minimum": friction.minimum,
                        "maximum": friction.maximum,
                        "below_0_08_count": below_count,
                        "sampled_count": friction.sampled,
                        "sample_is_complete": friction.sampled == friction.count,
                    },
                    "Solver既定値ではなく、入力Point Attributeの最終値を確認してください。",
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
                moving_names: List[str] = []
                if names is not None and len(names.values) == len(stat.values):
                    for piece_name, value in zip(names.values, stat.values):
                        if (_vector_length(value) or 0.0) > 1e-5:
                            moving_names.append(str(piece_name))
                self.add_issue(
                    "RBD_NONZERO_INITIAL_" + name.upper(),
                    "warning",
                    "high",
                    "rbd",
                    owner_path,
                    "開始フレームの%s分布に非ゼロ要素があります" % name,
                    {
                        "frame": geometry.frame,
                        "moving_count": moving,
                        "sampled": stat.sampled,
                        "max_length": stat.vector_max_length,
                        "moving_name_sample": moving_names[:12],
                        "sample_is_complete": stat.sampled == stat.count,
                    },
                    "投射物・アニメーション由来の意図した初速か、静止ピースの残留値かをnameで分類してください。",
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
        deforming = collider.stat("point", "deforming")
        animated = collider.stat("point", "animated")
        if deforming is None and animated is None:
            self.add_issue(
                "RBD_COLLIDER_MOTION_FLAGS_MISSING",
                "notice",
                "medium",
                "rbd",
                owner_path,
                "外部コライダーにanimated/deforming属性が見当たりません",
                {"source": collider.node_path},
                "静止Colliderなら問題ありません。変形キャラクターならRBD Configureを確認してください。",
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
                self.add_issue(
                    "RBD_GLOBAL_AT_FRAME_BREAK",
                    "warning",
                    "high",
                    "rbd",
                    path,
                    "Breaking ThresholdがGroupなしで全Constraintを時刻破断します",
                    {"rule_index": index, "constraint_name": constraint_name, "frame": frame},
                    "局所破壊が必要ならGroupまたはImpact条件へ限定してください。",
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
            file_path = self._parm_string(
                node,
                ("file", "file1", "sopoutput", "outputfile", "filepath", "cachefile"),
                "",
            )
            if load_from_disk and file_path:
                expanded = str(_safe(lambda: hou.expandString(file_path), file_path))
                if not FRAME_TOKEN_RE.search(expanded) and not os.path.exists(os.path.normpath(expanded)):
                    self.add_issue(
                        "CACHE_LOAD_FILE_MISSING",
                        "error",
                        "high",
                        "cache",
                        path,
                        "Load from Diskが有効ですがCacheファイルがありません",
                        {"path": expanded},
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


def render_llm_brief(report: Dict[str, Any], limit: int = 20) -> str:
    summary = report.get("summary", {})
    scene = report.get("scene", {})
    options = report.get("options", {})
    issues = list(report.get("issues", []))[: max(1, limit)]
    checks = list(report.get("checks", []))
    check_order = {"fail": 0, "review": 1, "pass": 2, "not_checked": 3}
    checks.sort(key=lambda item: (check_order.get(str(item.get("status", "")), 9), item.get("check_id", ""), item.get("node_path", "")))
    lines = [
        "# Houdini Preflight Evidence Packet",
        "",
        "## Instructions for the receiving LLM",
        "",
        "- `evidence`と`observed`だけを測定事実として扱う。",
        "- `tool_label`と`next_check`はヒューリスティックであり、原因や不具合の確定ではない。",
        "- `PASS`は記載された契約だけの合格、`FAIL`は明示契約違反、`REVIEW`は未確定候補、`NOT_CHECKED`は証拠不足を表す。",
        "- 要素数・Class・分布の入出力差だけから、属性消失・破損・因果関係を推定しない。identity集合差や契約FAILを優先する。",
        "- 最終回答を `確認済み / 候補 / 不明` に分け、証拠のない断定をしない。",
        "",
        "## Scan Context",
        "",
        "- HIP: `%s`" % scene.get("hip_file", ""),
        "- Frame: `%s`" % scene.get("frame", ""),
        "- Profile / scan: `%s / %s`" % (options.get("profile", ""), options.get("scan_level", "")),
        "- Scope node count: %s" % summary.get("node_count", 0),
        "- Contract checks: %s" % summary.get("check_count", len(checks)),
        "- Review records: %s" % summary.get("issue_count", 0),
        "",
        "## Contract Checks",
        "",
    ]
    if not checks:
        lines.append("- status=NOT_CHECKED check_id=NO_EXPLICIT_CONTRACT_CHECKS")
    for check in checks[:16]:
        evidence = json.dumps(
            _compact_llm_value(check.get("evidence") or {}),
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
    lines.extend(["", "## Requested judgement format", "", "1. 確認済み: PASS/FAILとobservedで直接支持される内容", "2. 候補: REVIEWから考えられる内容。反証候補も併記", "3. 不明: このpacketだけでは決められない内容", "4. 次に確認するノードと属性を最大5件"])
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
            " RBDはGeometry/Constraint/Proxy、APEX/KineFXはGraph/Port/Joint/Transform/Captureを重点検査します。"
            " LLM向け出力はPASS/FAIL/REVIEWと実測値を分離します。自動修正やシーン保存は行いません。"
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
            ("開始直後に爆散", "frame_one_explosion"),
            ("高速物体がすり抜ける", "tunneling"),
            ("滑りすぎる", "sliding"),
            ("Glue / Clusterがおかしい", "glue"),
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
