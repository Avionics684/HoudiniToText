"""Export a Houdini scene/network to Markdown and JSON for LLM inspection.

This script is intended to run inside Houdini 21 or hython. The command-line
exporter uses the standard library and hou; the optional UI uses PySide.
"""

from __future__ import annotations

import argparse
import datetime as _datetime
import hashlib
import json
import os
import re
import sys
import traceback
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Tuple

try:
    import hou  # type: ignore
except ImportError:  # Allows syntax checks outside Houdini.
    hou = None  # type: ignore


SCHEMA_VERSION = "1.17.3"
EXPORTER_NAME = "houdini_scene_to_text"
DEFAULT_MAX_TEXT_CHARS = 200_000
DEFAULT_GEOMETRY_SAMPLE_COUNT = 0
DEFAULT_GEOMETRY_NODE_MODE = "important"
DEFAULT_MARKDOWN_MODE = "compact"
DEFAULT_COMPACT_PARAMETER_LIMIT = 24
DEFAULT_EVALUATE_PARAMETERS = True
DEFAULT_INCLUDE_PACKED_RIG_TREES = True
DEFAULT_INCLUDE_BYPASSED_NODES = False
DEFAULT_INCLUDE_SCENE_PATHS = False
EXPORT_FRESHNESS_NOTICE_JA = "ファイルキャッシュなどは毎回きちんと更新しています。"
PARAMETER_SILENT_NODE_TYPES = {"null", "merge"}
WRANGLE_RUN_OVER_BY_INDEX = {
    0: "Detail (only once)",
    1: "Primitives",
    2: "Points",
    3: "Vertices",
    4: "Numbers",
}

STANDARD_ATTRIBUTE_NAMES_BY_OWNER = {
    "point": {
        "p",
        "pw",
        "n",
        "up",
        "uv",
        "uv2",
        "uv3",
        "cd",
        "alpha",
        "v",
        "accel",
        "force",
        "rest",
        "rest2",
        "orient",
        "rot",
        "scale",
        "pscale",
        "width",
    },
    "vertex": {"n", "uv", "uv2", "uv3", "cd", "alpha"},
    "primitive": set(),
    "global": set(),
}

CODE_NAME_HINTS = (
    "snippet",
    "code",
    "script",
    "python",
    "vfl",
    "osl",
    "callback",
    "kernel",
)

CODE_TEXT_HINTS = (
    ";\n",
    "def ",
    "class ",
    "import ",
    "return ",
    "#include",
    "hou.",
)


def _text_looks_like_code(text: str) -> bool:
    """Recognize executable source without mistaking group/path expressions for code."""
    if any(hint in text for hint in CODE_TEXT_HINTS):
        return True
    if re.search(r"(?m)^\s*(?:from\s+\S+\s+import|if\b.*:|for\b.*:|while\b.*:|try\s*:|with\b.*:)\s*$", text):
        return True
    # VEX snippets commonly contain attribute writes and a semicolon. A group
    # pattern such as @name=piece is not executable code and has no semicolon.
    if ";" in text and re.search(r"@[A-Za-z_]\w*\s*(?:\[[^]]+\])?\s*(?:=|\+=|-=|\*=|/=)", text):
        return True
    if ";" in text and "{" in text and "}" in text:
        return True
    return False

PACKED_RIG_NODE_TYPE_HINTS = (
    "packfolder",
    "packedfoldersplit",
    "unpackfolder",
    "packcharacter",
    "characterpack",
    "characterio",
    "sceneaddcharacter",
    "sceneanimate",
    "testgeometry_crag",
)


def _now_iso() -> str:
    return _datetime.datetime.now().astimezone().isoformat(timespec="seconds")


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8", errors="replace")).hexdigest()


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _enum_to_string(value: Any) -> Optional[str]:
    if value is None:
        return None
    try:
        name = value.name()
        if name:
            return str(name)
    except Exception:
        pass
    return str(value)


def _method(obj: Any, name: str) -> Optional[Callable[..., Any]]:
    candidate = getattr(obj, name, None)
    if callable(candidate):
        return candidate
    return None


def _path_of(item: Any) -> Optional[str]:
    if item is None:
        return None
    for method_name in ("path", "name"):
        method = _method(item, method_name)
        if method is not None:
            try:
                return str(method())
            except Exception:
                continue
    return str(item)


def _connection_touches_paths(connection: Dict[str, Any], paths: set) -> bool:
    if connection.get("subnet_indirect_input") in paths:
        return True
    for endpoint_name in ("source", "target"):
        endpoint = connection.get(endpoint_name, {})
        if not isinstance(endpoint, dict):
            continue
        for key in ("node", "item"):
            path = endpoint.get(key)
            if path in paths:
                return True
    return False


def _connection_within_paths(connection: Dict[str, Any], paths: set) -> bool:
    source_path = _connection_endpoint_path(connection, "source")
    target_path = _connection_endpoint_path(connection, "target")
    return source_path in paths and target_path in paths


def _connection_endpoint_path(connection: Dict[str, Any], endpoint_name: str) -> Optional[str]:
    endpoint = connection.get(endpoint_name, {})
    if not isinstance(endpoint, dict):
        return None
    return endpoint.get("item") or endpoint.get("node")


def _node_type_token(value: Any) -> str:
    text = str(value or "").strip().lower()
    if "/" in text:
        text = text.rsplit("/", 1)[-1]
    if "::" in text:
        text = text.split("::", 1)[0]
    return text


def _node_type_record_suppresses_parameters(node_type: Dict[str, Any]) -> bool:
    if not isinstance(node_type, dict):
        return False
    category = _node_type_token(node_type.get("category"))
    name_with_category = str(node_type.get("name_with_category") or "").strip().lower()
    if category != "sop" and not name_with_category.startswith("sop/"):
        return False
    candidates = {
        _node_type_token(node_type.get("name")),
        _node_type_token(node_type.get("name_with_category")),
        _node_type_token(node_type.get("description")),
    }
    return bool(candidates & PARAMETER_SILENT_NODE_TYPES)


def _connection_indices_equal(left: Any, right: Any) -> bool:
    if left == right:
        return True
    try:
        return int(left) == int(right)
    except Exception:
        return False


def _connection_index_is_zero(value: Any) -> bool:
    try:
        return int(value) == 0
    except Exception:
        return False


def _as_plain(value: Any, max_text_chars: int = DEFAULT_MAX_TEXT_CHARS) -> Any:
    """Convert HOM objects and enums into JSON-safe values."""
    if value is None or isinstance(value, (bool, int, float)):
        return value
    if isinstance(value, str):
        return _truncate_text(value, max_text_chars)
    if isinstance(value, bytes):
        return {
            "kind": "bytes",
            "length": len(value),
            "sha256": _sha256_bytes(value),
        }
    if isinstance(value, (list, tuple, set)):
        return [_as_plain(v, max_text_chars) for v in value]
    if isinstance(value, dict):
        return {str(_as_plain(k, max_text_chars)): _as_plain(v, max_text_chars) for k, v in value.items()}
    for method_name in ("path", "name"):
        method = _method(value, method_name)
        if method is not None:
            try:
                return str(method())
            except Exception:
                pass
    try:
        return str(value)
    except Exception:
        return repr(value)


_NUMERIC_LITERAL_RE = re.compile(
    r"^[+-]?(?:(?:\d+(?:\.\d*)?)|(?:\.\d+))(?:[eE][+-]?\d+)?$"
)


def _is_trivial_expression_source(source: Any) -> bool:
    """Return True for literals that convey no more information than their value."""
    return isinstance(source, str) and bool(_NUMERIC_LITERAL_RE.fullmatch(source.strip()))


def _parm_record_expression_source(parm_record: Dict[str, Any]) -> Any:
    """Return unevaluated parameter text when it represents an expression/source."""
    source_text = parm_record.get("source_text")
    if source_text not in (None, "") and not _is_trivial_expression_source(source_text):
        return source_text

    expression = parm_record.get("expression")
    if expression not in (None, "") and not _is_trivial_expression_source(expression):
        return expression

    raw_value = parm_record.get("raw_value")
    if (
        parm_record.get("is_showing_expression")
        and raw_value not in (None, "")
        and not _is_trivial_expression_source(raw_value)
    ):
        return raw_value

    keyframes = parm_record.get("keyframes", []) or []
    if any(keyframe.get("expression") not in (None, "") for keyframe in keyframes):
        keyframe_expressions = [
            keyframe.get("expression")
            for keyframe in keyframes
            if keyframe.get("expression") not in (None, "")
            and not _is_trivial_expression_source(keyframe.get("expression"))
        ]
        if not keyframe_expressions:
            return None
        # rawValue() normally returns the active key's source, but do not let a
        # UI/evaluation-state numeric value replace the source found directly
        # on the keyframes.
        if raw_value in keyframe_expressions:
            return raw_value
        return keyframe_expressions[0]

    # String parameters can contain $ variables and backtick expressions
    # without owning an animation channel/keyframe.
    unexpanded = parm_record.get("unexpanded_string")
    if isinstance(unexpanded, str) and ("$" in unexpanded or "`" in unexpanded):
        return unexpanded
    return None


_CHANNEL_REFERENCE_RE = re.compile(
    r"\b(?:ch|chf|chi|chramp|chs|chsop|chv|chp|chop)\s*\(",
    re.IGNORECASE,
)
_KEYFRAME_INTERPOLATION_RE = re.compile(
    r"^\s*(?:bezier|constant|cubic|cycle|cycleoffset|linear|match|qlinear|spline|vmatch)\s*\(",
    re.IGNORECASE,
)


def _expression_source_kind(source: Any, language: Any = None) -> Optional[str]:
    """Classify source for readability without restricting what is captured."""
    if source in (None, "") or _is_trivial_expression_source(source):
        return None
    text = str(source)
    language_text = str(language or "").lower()
    if _KEYFRAME_INTERPOLATION_RE.search(text):
        return "keyframe_interpolation"
    if _CHANNEL_REFERENCE_RE.search(text):
        return "channel_reference"
    if "`" in text:
        return "string_backtick_expression"
    if "$" in text:
        return "hscript_variable"
    if "python" in language_text:
        return "python_expression"
    if "hscript" in language_text:
        return "hscript_expression"
    return "expression"


def _truncate_text(text: str, max_text_chars: int = DEFAULT_MAX_TEXT_CHARS) -> str:
    if max_text_chars is None or max_text_chars <= 0 or len(text) <= max_text_chars:
        return text
    keep = max(0, max_text_chars)
    return (
        text[:keep]
        + "\n\n[TRUNCATED: original_chars=%d sha256=%s]"
        % (len(text), _sha256_text(text))
    )


def _maybe_long_text_record(text: str, max_text_chars: int) -> Dict[str, Any]:
    return {
        "text": _truncate_text(text, max_text_chars),
        "length": len(text),
        "sha256": _sha256_text(text),
        "truncated": max_text_chars > 0 and len(text) > max_text_chars,
    }


def _is_probably_text(data: bytes) -> bool:
    if not data:
        return True
    sample = data[:4096]
    if b"\x00" in sample:
        return False
    try:
        sample.decode("utf-8")
        return True
    except UnicodeDecodeError:
        pass
    printable = sum(1 for b in sample if b in b"\n\r\t" or 32 <= b <= 126)
    return printable / float(len(sample)) > 0.85


def _sanitize_filename(value: str) -> str:
    value = re.sub(r"[^A-Za-z0-9_.-]+", "_", value.strip())
    return value.strip("_") or "houdini_scene"


def _json_dump(data: Dict[str, Any], path: str) -> None:
    with open(path, "w", encoding="utf-8") as handle:
        json.dump(data, handle, indent=2, ensure_ascii=False, sort_keys=False)
        handle.write("\n")


def _write_text(text: str, path: str) -> None:
    with open(path, "w", encoding="utf-8", newline="\n") as handle:
        handle.write(text)


class HoudiniSceneExporter:
    def __init__(
        self,
        root_paths: Optional[Sequence[str]] = None,
        node_paths: Optional[Sequence[str]] = None,
        include_hidden_parms: bool = False,
        changed_only: bool = False,
        evaluate_parameters: bool = DEFAULT_EVALUATE_PARAMETERS,
        include_node_status: bool = False,
        include_parameter_state: bool = False,
        recurse_locked_nodes: bool = False,
        sync_delayed_definitions: bool = False,
        hda_section_mode: str = "none",
        max_text_chars: int = DEFAULT_MAX_TEXT_CHARS,
        include_geometry_summary: bool = False,
        geometry_sample_count: int = DEFAULT_GEOMETRY_SAMPLE_COUNT,
        geometry_node_mode: str = DEFAULT_GEOMETRY_NODE_MODE,
        include_private_attributes: bool = False,
        include_standard_attributes: bool = False,
        include_packed_rig_trees: bool = DEFAULT_INCLUDE_PACKED_RIG_TREES,
        include_bypassed_nodes: bool = DEFAULT_INCLUDE_BYPASSED_NODES,
        include_scene_paths: bool = DEFAULT_INCLUDE_SCENE_PATHS,
        include_network_items: bool = False,
        temporary_frame: Optional[float] = None,
    ) -> None:
        self.root_paths = list(root_paths or ["/"])
        self.node_paths = list(node_paths or [])
        self.include_hidden_parms = include_hidden_parms
        self.changed_only = changed_only
        self.evaluate_parameters = evaluate_parameters
        self.include_node_status = include_node_status
        self.include_parameter_state = include_parameter_state
        self.recurse_locked_nodes = recurse_locked_nodes
        self.sync_delayed_definitions = sync_delayed_definitions
        self.hda_section_mode = hda_section_mode
        self.max_text_chars = max_text_chars
        self.include_geometry_summary = include_geometry_summary
        self.geometry_sample_count = geometry_sample_count
        self.geometry_node_mode = geometry_node_mode
        self.include_private_attributes = include_private_attributes
        self.include_standard_attributes = include_standard_attributes
        self.include_packed_rig_trees = include_packed_rig_trees
        self.include_bypassed_nodes = include_bypassed_nodes
        self.include_scene_paths = include_scene_paths
        self.include_network_items = include_network_items
        self.temporary_frame = temporary_frame
        self.errors: List[Dict[str, Any]] = []
        self._connection_keys: set = set()
        self._definition_keys: set = set()
        self._hda_definitions: List[Dict[str, Any]] = []
        self._geometry_cache: Dict[str, Any] = {}

    def export(self) -> Dict[str, Any]:
        if hou is None:
            raise RuntimeError("This exporter must run inside Houdini or hython where the hou module is available.")
        if self.temporary_frame is not None:
            original_frame = self._safe("hou.frame", lambda: hou.frame(), None)
            self._safe("hou.setFrame(%s)" % self.temporary_frame, lambda: hou.setFrame(self.temporary_frame), None)
            try:
                return self._export_at_current_frame()
            finally:
                if original_frame is not None:
                    self._safe("hou.setFrame(%s)" % original_frame, lambda: hou.setFrame(original_frame), None)
        return self._export_at_current_frame()

    def _export_at_current_frame(self) -> Dict[str, Any]:
        if self.node_paths:
            roots = self._resolve_nodes(self.node_paths)
            nodes = roots
            network_items = []
        else:
            roots = self._resolve_roots(self.root_paths)
            nodes = self._collect_nodes(roots)
            network_items = self._collect_network_items(roots, nodes)
        skipped_bypassed_paths = set()
        if not self.include_bypassed_nodes:
            skipped_bypassed_paths = {path for path in (_path_of(node) for node in nodes if self._node_is_bypassed(node)) if path}
            nodes_for_export = [node for node in nodes if _path_of(node) not in skipped_bypassed_paths]
        else:
            nodes_for_export = nodes
        dot_paths = {path for path in (_path_of(item) for item in network_items if self._network_item_is_dot(item)) if path}
        connections = self._collect_connections(nodes, network_items)
        connections = self._collapse_network_dot_connections(connections, dot_paths)
        if skipped_bypassed_paths:
            connections = self._connections_with_skipped_bypassed_nodes(connections, skipped_bypassed_paths)
        if self.node_paths:
            allowed_paths = {path for path in (_path_of(node) for node in nodes_for_export) if path}
            resolved_connections = []
            seen_keys = set()
            for connection in connections:
                record = self._connection_resolved_to_nodes(connection, allowed_paths)
                if not _connection_within_paths(record, allowed_paths):
                    continue
                key = record.get("key")
                if key and key in seen_keys:
                    continue
                if key:
                    seen_keys.add(key)
                resolved_connections.append(record)
            connections = resolved_connections

        node_records: List[Dict[str, Any]] = []
        code_blocks: List[Dict[str, Any]] = []
        for node in nodes_for_export:
            record = self._node_record(node)
            node_records.append(record)
            code_blocks.extend(record.get("code_blocks", []))

        if self.include_network_items:
            network_item_records = [self._network_item_record(item) for item in network_items]
        else:
            # Sticky notes, network boxes and dots are visual layout aids;
            # dots are already collapsed into direct connections above.
            network_item_records = []

        data = {
            "schema_version": SCHEMA_VERSION,
            "exporter": {
                "name": EXPORTER_NAME,
                "created_at": _now_iso(),
                "python_version": sys.version,
            },
            "scene": self._scene_record(),
            "options": {
                "root_paths": self.root_paths,
                "node_paths": self.node_paths,
                "include_hidden_parms": self.include_hidden_parms,
                "changed_only": self.changed_only,
                "evaluate_parameters": self.evaluate_parameters,
                "include_node_status": self.include_node_status,
                "include_parameter_state": self.include_parameter_state,
                "recurse_locked_nodes": self.recurse_locked_nodes,
                "sync_delayed_definitions": self.sync_delayed_definitions,
                "hda_section_mode": self.hda_section_mode,
                "max_text_chars": self.max_text_chars,
                "include_geometry_summary": self.include_geometry_summary,
                "geometry_sample_count": self.geometry_sample_count,
                "geometry_node_mode": self.geometry_node_mode,
                "include_private_attributes": self.include_private_attributes,
                "include_standard_attributes": self.include_standard_attributes,
                "include_packed_rig_trees": self.include_packed_rig_trees,
                "include_bypassed_nodes": self.include_bypassed_nodes,
                "include_scene_paths": self.include_scene_paths,
                "include_network_items": self.include_network_items,
                "temporary_frame": self.temporary_frame,
            },
            "counts": {
                "roots": len(roots),
                "nodes": len(node_records),
                "connections": len(connections),
                "network_items": len(network_item_records),
                "network_dots_collapsed": len(dot_paths),
                "code_blocks": len(code_blocks),
                "hda_definitions": len(self._hda_definitions),
                "packed_rig_trees": sum(1 for record in node_records if record.get("packed_rig_tree")),
                "bypassed_nodes_skipped": len(skipped_bypassed_paths),
                "errors": len(self.errors),
            },
            "roots": [_path_of(root) for root in roots],
            "nodes": node_records,
            "connections": connections,
            "network_items": network_item_records,
            "code_blocks": code_blocks,
            "hda_definitions": self._hda_definitions,
            "notes": [EXPORT_FRESHNESS_NOTICE_JA],
            "errors": self.errors,
        }
        return data

    def _node_is_bypassed(self, node: Any) -> bool:
        return bool(self._try_method(node, "isBypassed", False))

    def _safe(self, context: str, func: Callable[[], Any], default: Any = None) -> Any:
        try:
            return func()
        except Exception as exc:
            self.errors.append(
                {
                    "context": context,
                    "error_type": exc.__class__.__name__,
                    "message": str(exc),
                }
            )
            return default

    def _safe_method(self, obj: Any, method_name: str, default: Any = None, *args: Any) -> Any:
        method = _method(obj, method_name)
        if method is None:
            return default
        return self._safe("%s.%s" % (_path_of(obj) or obj.__class__.__name__, method_name), lambda: method(*args), default)

    def _try_method(self, obj: Any, method_name: str, default: Any = None, *args: Any) -> Any:
        method = _method(obj, method_name)
        if method is None:
            return default
        try:
            return method(*args)
        except Exception:
            return default

    def _resolve_roots(self, root_paths: Sequence[str]) -> List[Any]:
        roots = []
        for path in root_paths:
            node = self._safe("hou.node(%s)" % path, lambda p=path: hou.node(p), None)
            if node is None:
                self.errors.append({"context": "root", "error_type": "MissingNode", "message": "No node at %s" % path})
                continue
            roots.append(node)
        return roots

    def _resolve_nodes(self, node_paths: Sequence[str]) -> List[Any]:
        nodes = []
        seen = set()
        for path in node_paths:
            if path in seen:
                continue
            seen.add(path)
            node = self._safe("hou.node(%s)" % path, lambda p=path: hou.node(p), None)
            if node is None:
                self.errors.append({"context": "node", "error_type": "MissingNode", "message": "No node at %s" % path})
                continue
            nodes.append(node)
        return nodes

    def _collect_nodes(self, roots: Sequence[Any]) -> List[Any]:
        seen: set = set()
        nodes: List[Any] = []

        def add_node(node: Any) -> None:
            path = _path_of(node)
            if not path or path in seen:
                return
            seen.add(path)
            nodes.append(node)

        def walk(node: Any) -> None:
            add_node(node)
            children = self._safe_method(node, "children", (),)
            for child in children or ():
                walk(child)

        for root in roots:
            add_node(root)
            all_sub_children = _method(root, "allSubChildren")
            if all_sub_children is not None:
                children = self._safe(
                    "%s.allSubChildren" % (_path_of(root) or "<root>"),
                    lambda r=root: r.allSubChildren(
                        top_down=True,
                        recurse_in_locked_nodes=self.recurse_locked_nodes,
                        sync_delayed_definition=self.sync_delayed_definitions,
                    ),
                    (),
                )
                for child in children or ():
                    add_node(child)
            else:
                walk(root)
        return nodes

    def _collect_network_items(self, roots: Sequence[Any], nodes: Sequence[Any]) -> List[Any]:
        node_paths = {_path_of(node) for node in nodes}
        seen: set = set()
        items: List[Any] = []
        for root in roots:
            all_sub_items = _method(root, "allSubItems")
            raw_items = ()
            if all_sub_items is not None:
                raw_items = self._safe(
                    "%s.allSubItems" % (_path_of(root) or "<root>"),
                    lambda r=root: r.allSubItems(
                        top_down=True,
                        recurse_in_locked_nodes=self.recurse_locked_nodes,
                        sync_delayed_definition=self.sync_delayed_definitions,
                    ),
                    (),
                )
            else:
                all_items = _method(root, "allItems")
                if all_items is not None:
                    raw_items = self._safe("%s.allItems" % (_path_of(root) or "<root>"), lambda r=root: r.allItems(), ())

            for item in raw_items or ():
                path = _path_of(item)
                if not path or path in seen or path in node_paths:
                    continue
                seen.add(path)
                items.append(item)
        return items

    def _collect_connections(self, nodes: Sequence[Any], network_items: Sequence[Any]) -> List[Dict[str, Any]]:
        records: List[Dict[str, Any]] = []
        for item in list(nodes) + list(network_items):
            for method_name in ("inputConnections", "outputConnections"):
                connections = self._safe_method(item, method_name, ())
                for connection in connections or ():
                    record = self._connection_record(connection)
                    key = record.get("key")
                    if key and key not in self._connection_keys:
                        self._connection_keys.add(key)
                        records.append(record)
        records.sort(key=lambda row: str(row.get("key", "")))
        return records

    def _connection_resolved_to_nodes(self, connection: Dict[str, Any], allowed_paths: set) -> Dict[str, Any]:
        """When an endpoint item (e.g. a network dot) is outside the export set but hou
        resolved the real node, swap the item for the node so the connection survives."""
        source = dict(connection.get("source", {}) or {})
        target = dict(connection.get("target", {}) or {})
        changed = False
        for endpoint in (source, target):
            item = endpoint.get("item")
            node = endpoint.get("node")
            if item and node and item != node and item not in allowed_paths and node in allowed_paths:
                endpoint["item"] = node
                if endpoint is source and endpoint.get("node_output_index") is not None:
                    endpoint["output_index"] = endpoint["node_output_index"]
                changed = True
        if not changed:
            return connection
        record = dict(connection)
        record["source"] = source
        record["target"] = target
        record["key"] = "%s:%s->%s:%s" % (
            source.get("item"),
            source.get("output_index"),
            target.get("item"),
            target.get("input_index"),
        )
        return record

    def _network_item_is_dot(self, item: Any) -> bool:
        if item.__class__.__name__ == "NetworkDot":
            return True
        item_type = _enum_to_string(self._try_method(item, "networkItemType", None))
        return str(item_type or "").endswith("NetworkDot")

    def _collapse_network_dot_connections(self, connections: Sequence[Dict[str, Any]], dot_paths: set) -> List[Dict[str, Any]]:
        """Rewrite connections so wires routed through network dots read as direct node-to-node links."""
        if not dot_paths:
            return list(connections)

        incoming_by_dot: Dict[str, Dict[str, Any]] = {}
        for connection in connections:
            target_path = _connection_endpoint_path(connection, "target")
            if target_path in dot_paths:
                existing = incoming_by_dot.get(target_path)
                if existing is None or str(connection.get("key", "")) < str(existing.get("key", "")):
                    incoming_by_dot[target_path] = connection

        def resolve_upstream(dot_path: str) -> Tuple[Optional[Dict[str, Any]], List[str]]:
            via: List[str] = []
            current = dot_path
            while current in dot_paths:
                if current in via:
                    return None, via  # Cycle of dots; drop rather than loop forever.
                via.append(current)
                connection = incoming_by_dot.get(current)
                if connection is None:
                    return None, via  # Dangling dot with no input.
                source_path = _connection_endpoint_path(connection, "source")
                if source_path in dot_paths:
                    current = source_path
                    continue
                return connection, via
            return None, via

        records: List[Dict[str, Any]] = []
        keys: set = set()
        for connection in connections:
            source_path = _connection_endpoint_path(connection, "source")
            target_path = _connection_endpoint_path(connection, "target")
            if target_path in dot_paths:
                continue  # Re-emitted from the dot's outgoing side as a collapsed connection.
            if source_path not in dot_paths:
                key = connection.get("key")
                if key and key in keys:
                    continue
                if key:
                    keys.add(key)
                records.append(connection)
                continue
            upstream, via = resolve_upstream(source_path)
            if upstream is not None:
                source = dict(upstream.get("source", {}) or {})
            else:
                # No dot-to-dot segments were collected (hou dots expose no
                # inputConnections). hou already resolves the real upstream
                # node into NodeConnection.inputNode(), recorded as source.node.
                upstream_node = (connection.get("source", {}) or {}).get("node")
                if not upstream_node or upstream_node in dot_paths:
                    continue
                source = dict(connection.get("source", {}) or {})
                source["item"] = upstream_node
                if source.get("node_output_index") is not None:
                    source["output_index"] = source["node_output_index"]
            target = dict(connection.get("target", {}) or {})
            key = "%s:%s->%s:%s" % (
                source.get("item") or source.get("node"),
                source.get("output_index"),
                target.get("item") or target.get("node"),
                target.get("input_index"),
            )
            if key in keys:
                continue
            keys.add(key)
            records.append(
                {
                    "key": key,
                    "source": source,
                    "target": target,
                    "subnet_indirect_input": None,
                    "selected": None,
                    "class": "CollapsedDotConnection",
                    "synthetic": True,
                    "reason": "network_dots_collapsed",
                    "via_dots": list(reversed(via)),
                }
            )
        records.sort(key=lambda row: str(row.get("key", "")))
        return records

    def _connections_with_skipped_bypassed_nodes(self, connections: Sequence[Dict[str, Any]], skipped_paths: set) -> List[Dict[str, Any]]:
        records: List[Dict[str, Any]] = []
        keys = set()
        for connection in connections:
            if _connection_touches_paths(connection, skipped_paths):
                continue
            key = connection.get("key")
            if key:
                keys.add(key)
            records.append(connection)

        for connection in self._synthetic_bypassed_connections(connections, skipped_paths):
            key = connection.get("key")
            if key and key in keys:
                continue
            if key:
                keys.add(key)
            records.append(connection)

        records.sort(key=lambda row: str(row.get("key", "")))
        return records

    def _synthetic_bypassed_connections(self, connections: Sequence[Dict[str, Any]], skipped_paths: set) -> List[Dict[str, Any]]:
        outgoing_by_source: Dict[str, List[Dict[str, Any]]] = {}
        entry_connections: List[Dict[str, Any]] = []
        for connection in connections:
            source_path = _connection_endpoint_path(connection, "source")
            target_path = _connection_endpoint_path(connection, "target")
            if source_path in skipped_paths:
                outgoing_by_source.setdefault(source_path, []).append(connection)
            if target_path in skipped_paths and source_path not in skipped_paths:
                entry_connections.append(connection)

        for source_connections in outgoing_by_source.values():
            source_connections.sort(key=lambda row: str(row.get("key", "")))
        entry_connections.sort(key=lambda row: str(row.get("key", "")))

        records: List[Dict[str, Any]] = []
        keys = set()
        for entry_connection in entry_connections:
            first_bypassed_path = _connection_endpoint_path(entry_connection, "target")
            if not first_bypassed_path:
                continue
            self._walk_bypassed_connection_routes(
                source_connection=entry_connection,
                current_connection=entry_connection,
                current_bypassed_path=first_bypassed_path,
                bypassed_paths=[first_bypassed_path],
                outgoing_by_source=outgoing_by_source,
                skipped_paths=skipped_paths,
                records=records,
                keys=keys,
            )
        return records

    def _walk_bypassed_connection_routes(
        self,
        source_connection: Dict[str, Any],
        current_connection: Dict[str, Any],
        current_bypassed_path: str,
        bypassed_paths: List[str],
        outgoing_by_source: Dict[str, List[Dict[str, Any]]],
        skipped_paths: set,
        records: List[Dict[str, Any]],
        keys: set,
    ) -> None:
        if len(bypassed_paths) > len(skipped_paths):
            return

        outgoing_connections = self._bypassed_outgoing_connections_for_input(
            current_connection,
            outgoing_by_source.get(current_bypassed_path, []),
        )
        for outgoing_connection in outgoing_connections:
            target_path = _connection_endpoint_path(outgoing_connection, "target")
            if not target_path:
                continue
            if target_path in skipped_paths:
                if target_path in bypassed_paths:
                    continue
                self._walk_bypassed_connection_routes(
                    source_connection=source_connection,
                    current_connection=outgoing_connection,
                    current_bypassed_path=target_path,
                    bypassed_paths=bypassed_paths + [target_path],
                    outgoing_by_source=outgoing_by_source,
                    skipped_paths=skipped_paths,
                    records=records,
                    keys=keys,
                )
                continue

            record = self._synthetic_bypassed_connection_record(source_connection, outgoing_connection, bypassed_paths)
            key = record.get("key")
            if key and key in keys:
                continue
            if key:
                keys.add(key)
            records.append(record)

    def _bypassed_outgoing_connections_for_input(
        self,
        incoming_connection: Dict[str, Any],
        outgoing_connections: Sequence[Dict[str, Any]],
    ) -> List[Dict[str, Any]]:
        if not outgoing_connections:
            return []

        target = incoming_connection.get("target", {})
        input_index = target.get("input_index") if isinstance(target, dict) else None
        if input_index is None:
            return list(outgoing_connections)

        exact_matches = []
        primary_matches = []
        for connection in outgoing_connections:
            source = connection.get("source", {})
            output_index = source.get("output_index") if isinstance(source, dict) else None
            if _connection_indices_equal(input_index, output_index):
                exact_matches.append(connection)
            elif _connection_index_is_zero(input_index) and (output_index is None or _connection_index_is_zero(output_index)):
                primary_matches.append(connection)
        if exact_matches:
            return exact_matches
        if primary_matches:
            return primary_matches
        return []

    def _synthetic_bypassed_connection_record(
        self,
        source_connection: Dict[str, Any],
        target_connection: Dict[str, Any],
        bypassed_paths: Sequence[str],
    ) -> Dict[str, Any]:
        source = dict(source_connection.get("source", {}) or {})
        target = dict(target_connection.get("target", {}) or {})
        source_path = source.get("item") or source.get("node")
        target_path = target.get("item") or target.get("node")
        key = "%s:%s->%s:%s" % (
            source_path,
            source.get("output_index"),
            target_path,
            target.get("input_index"),
        )
        return {
            "key": key,
            "source": source,
            "target": target,
            "subnet_indirect_input": None,
            "selected": None,
            "class": "SyntheticBypassedConnection",
            "synthetic": True,
            "reason": "bypassed_nodes_skipped",
            "bypassed_nodes": list(bypassed_paths),
        }

    def _scene_record(self) -> Dict[str, Any]:
        frame_range = self._safe("hou.playbar.frameRange", lambda: hou.playbar.frameRange(), ())
        playback_range = self._safe("hou.playbar.playbackRange", lambda: hou.playbar.playbackRange(), ())
        record = {
            "houdini_version": self._safe("hou.applicationVersionString", lambda: hou.applicationVersionString(), None),
            "application_name": self._safe("hou.applicationName", lambda: hou.applicationName(), None),
            "fps": self._safe("hou.fps", lambda: hou.fps(), None),
            "current_frame": self._safe("hou.frame", lambda: hou.frame(), None),
            "current_time": self._safe("hou.time", lambda: hou.time(), None),
            "frame_range": _as_plain(frame_range, self.max_text_chars),
            "playback_range": _as_plain(playback_range, self.max_text_chars),
            "takes": self._takes_record(),
        }
        if self.include_scene_paths:
            record.update(
                {
                    "hip_file": self._safe("hou.hipFile.path", lambda: hou.hipFile.path(), ""),
                    "hip_name": self._safe("hou.hipFile.basename", lambda: hou.hipFile.basename(), None),
                    "hip_dir": self._safe("hou.getenv(HIP)", lambda: hou.getenv("HIP"), None),
                    "loaded_hda_files": self._safe("hou.hda.loadedFiles", lambda: list(hou.hda.loadedFiles()), []),
                }
            )
        return record

    def _takes_record(self) -> Dict[str, Any]:
        return {
            "current": self._safe("hou.takes.currentTake", lambda: hou.takes.currentTake().name(), None),
            "all": self._safe("hou.takes.takes", lambda: [take.name() for take in hou.takes.takes()], []),
        }

    def _node_record(self, node: Any) -> Dict[str, Any]:
        path = _path_of(node)
        node_type = self._node_type_record(node)
        flags = self._node_flags(node)
        if _node_type_record_suppresses_parameters(node_type):
            parm_records: List[Dict[str, Any]] = []
            code_blocks: List[Dict[str, Any]] = []
        else:
            parm_records, code_blocks = self._node_parameters(node)
        definition_key = self._capture_hda_definition(node)
        record = {
            "path": path,
            "name": self._safe_method(node, "name", None),
            "parent_path": _path_of(self._safe_method(node, "parent", None)),
            "class": node.__class__.__name__,
            "type": node_type,
            "hda_definition_key": definition_key,
            "is_network": self._safe_method(node, "isNetwork", None),
            "children": [_path_of(child) for child in self._safe_method(node, "children", ()) or ()],
            "position": _as_plain(self._safe_method(node, "position", None), self.max_text_chars),
            "size": _as_plain(self._safe_method(node, "size", None), self.max_text_chars),
            "color": _as_plain(self._safe_method(node, "color", None), self.max_text_chars),
            "comment": _as_plain(self._safe_method(node, "comment", ""), self.max_text_chars),
            "flags": flags,
            "user_data": _as_plain(self._safe_method(node, "userDataDict", {}), self.max_text_chars),
            "cached_user_data": _as_plain(self._safe_method(node, "cachedUserDataDict", {}), self.max_text_chars),
            "input_ports": self._ports_record(node, "input"),
            "output_ports": self._ports_record(node, "output"),
            "inputs": self._endpoint_list(node, "inputs"),
            "outputs": self._endpoint_list(node, "outputs"),
            "parameters": parm_records,
            "code_blocks": code_blocks,
        }
        if self.include_node_status:
            record["messages"] = {
                "errors": _as_plain(self._safe_method(node, "errors", ()), self.max_text_chars),
                "warnings": _as_plain(self._safe_method(node, "warnings", ()), self.max_text_chars),
                "messages": _as_plain(self._safe_method(node, "messages", ()), self.max_text_chars),
            }
        else:
            record["messages_skipped"] = "node status queries are disabled by default because they can trigger cooks"
        if self._should_include_geometry(node):
            geometry = self._geometry_summary(node)
            if geometry is not None:
                record["geometry_summary"] = geometry
        if self._should_include_packed_rig_tree(node, node_type, flags):
            packed_rig_tree = self._packed_rig_tree(node)
            if packed_rig_tree is not None:
                record["packed_rig_tree"] = packed_rig_tree
        return record

    def _node_geometry(self, node: Any) -> Any:
        path = _path_of(node) or "<node:%s>" % id(node)
        if path in self._geometry_cache:
            return self._geometry_cache[path]
        geometry_method = _method(node, "geometry")
        if geometry_method is None:
            self._geometry_cache[path] = None
            return None
        geometry = self._safe("%s.geometry" % path, lambda: geometry_method(), None)
        self._geometry_cache[path] = geometry
        return geometry

    def _should_include_packed_rig_tree(
        self,
        node: Any,
        node_type: Dict[str, Any],
        flags: Dict[str, Any],
    ) -> bool:
        if not self.include_packed_rig_trees or _method(node, "geometry") is None:
            return False
        # Geometry-summary modes have already opted into cooking this node, so
        # checking packed paths adds no extra cook. In normal compact/verbose
        # mode, only known packed-character producers are queried.
        if self._should_include_geometry(node):
            return True
        # The displayed/rendered SOP is normally already cooked by Houdini.
        # Querying it catches packed hierarchies produced by ordinary SOPs,
        # including Test Geometry: Crag, without probing every node upstream.
        if flags.get("isDisplayFlagSet") is True or flags.get("isRenderFlagSet") is True:
            return True
        type_text = " ".join(
            str(node_type.get(key) or "").lower()
            for key in ("name", "name_with_category", "description")
        )
        return any(hint in type_text for hint in PACKED_RIG_NODE_TYPE_HINTS)

    def _packed_rig_tree(self, node: Any) -> Optional[Dict[str, Any]]:
        geometry = self._node_geometry(node)
        if geometry is None:
            return None
        extract_paths = _method(geometry, "extractPackedPaths")
        if extract_paths is None:
            return None
        try:
            raw_paths = extract_paths("*")
        except Exception:
            return None
        paths = sorted(
            normalized
            for normalized in {
                self._normalize_packed_path(path)
                for path in raw_paths or ()
                if str(path or "").strip()
            }
            if normalized != "/"
        )
        if not paths:
            return None

        folders: set = set()
        for path in paths:
            components = [part for part in path.strip("/").split("/") if part]
            for index in range(1, len(components)):
                folders.add("/" + "/".join(components[:index]))
            if components and components[-1].lower().endswith((".char", ".ctrl")):
                folders.add(path)

        properties: Dict[str, Any] = {}
        properties_method = _method(geometry, "packedFolderProperties")
        if properties_method is not None:
            for path in sorted(set(paths) | folders):
                try:
                    value = properties_method(path)
                except Exception:
                    continue
                if value:
                    plain_value = _as_plain(value, self.max_text_chars)
                    properties[path] = plain_value
                    if self._packed_properties_mark_folder(plain_value):
                        folders.add(path)

        return {
            "source": "hou.Geometry.extractPackedPaths('*')",
            "paths": paths,
            "folders": sorted(folders),
            "properties": properties,
        }

    def _normalize_packed_path(self, value: Any) -> str:
        text = str(value).replace("\\", "/").strip()
        if not text.startswith("/"):
            text = "/" + text
        text = re.sub(r"/+", "/", text)
        return text.rstrip("/") or "/"

    def _packed_properties_mark_folder(self, value: Any) -> bool:
        if not isinstance(value, dict):
            return False
        for key, item in value.items():
            normalized_key = re.sub(r"[^a-z]", "", str(key).lower())
            if normalized_key in ("folder", "isfolder", "treatasfolder"):
                return bool(item)
        return False

    def _should_include_geometry(self, node: Any) -> bool:
        if not self.include_geometry_summary or self.geometry_node_mode == "none":
            return False
        if _method(node, "geometry") is None:
            return False
        if self.geometry_node_mode == "all":
            return True

        path = _path_of(node)
        if path in self.root_paths and path not in ("/", "/obj", "/stage", "/out", "/mat", "/shop", "/img", "/tasks"):
            return True
        for method_name in ("isDisplayFlagSet", "isRenderFlagSet", "isSelected", "isCurrent"):
            if self._try_method(node, method_name, False):
                return True

        node_type = self._try_method(node, "type", None)
        type_name = str(self._try_method(node_type, "name", "") or "").lower()
        type_with_category = str(self._try_method(node_type, "nameWithCategory", "") or "").lower()
        important_type_hints = ("output", "null", "filecache", "rop_geometry", "geometryrop", "cache")
        return any(hint in type_name or hint in type_with_category for hint in important_type_hints)

    def _node_type_record(self, node: Any) -> Dict[str, Any]:
        node_type = self._safe_method(node, "type", None)
        category = self._safe_method(node_type, "category", None) if node_type is not None else None
        definition = self._safe_method(node_type, "definition", None) if node_type is not None else None
        record = {
            "name": self._safe_method(node_type, "name", None) if node_type is not None else None,
            "name_with_category": self._safe_method(node_type, "nameWithCategory", None) if node_type is not None else None,
            "description": self._safe_method(node_type, "description", None) if node_type is not None else None,
            "category": self._safe_method(category, "name", None) if category is not None else None,
            "category_label": self._safe_method(category, "label", None) if category is not None else None,
            "icon": self._safe_method(node_type, "icon", None) if node_type is not None else None,
            "has_hda_definition": definition is not None,
        }
        if self.include_scene_paths and node_type is not None:
            record["source"] = self._safe_method(node_type, "sourcePath", None)
        return record

    def _node_flags(self, node: Any) -> Dict[str, Any]:
        flags = {}
        for method_name in (
            "isSelected",
            "isCurrent",
            "isDisplayFlagSet",
            "isRenderFlagSet",
            "isTemplateFlagSet",
            "isBypassed",
            "isHardLocked",
            "isSoftLocked",
            "isLockedHDA",
            "isInsideLockedHDA",
            "matchesCurrentDefinition",
            "isEditable",
            "isEditableInsideLockedHDA",
        ):
            method = _method(node, method_name)
            if method is not None:
                flags[method_name] = self._safe_method(node, method_name, None)
        if self.include_parameter_state:
            method = _method(node, "isTimeDependent")
            if method is not None:
                flags["isTimeDependent"] = self._safe_method(node, "isTimeDependent", None)
        return flags

    def _ports_record(self, node: Any, direction: str) -> List[Dict[str, Any]]:
        if direction == "input":
            names_method, labels_method = "inputNames", "inputLabels"
        else:
            names_method, labels_method = "outputNames", "outputLabels"
        names = self._safe_method(node, names_method, ())
        labels = self._safe_method(node, labels_method, ())
        count = max(len(names or ()), len(labels or ()))
        records = []
        for index in range(count):
            records.append(
                {
                    "index": index,
                    "name": names[index] if names and index < len(names) else None,
                    "label": labels[index] if labels and index < len(labels) else None,
                }
            )
        return records

    def _endpoint_list(self, node: Any, method_name: str) -> List[Dict[str, Any]]:
        endpoints = self._safe_method(node, method_name, ())
        records = []
        for index, endpoint in enumerate(endpoints or ()):
            records.append({"index": index, "path": _path_of(endpoint) if endpoint is not None else None})
        return records

    def _connection_record(self, connection: Any) -> Dict[str, Any]:
        input_node = self._safe_method(connection, "inputNode", None)
        output_node = self._safe_method(connection, "outputNode", None)
        input_item = self._safe_method(connection, "inputItem", None)
        output_item = self._safe_method(connection, "outputItem", None)
        subnet_indirect = self._safe_method(connection, "subnetIndirectInput", None)
        source_path = _path_of(input_item) or _path_of(input_node)
        target_path = _path_of(output_item) or _path_of(output_node)
        item_output_index = self._try_method(connection, "inputItemOutputIndex", None)
        # outputIndex() resolves through network dots to the real upstream node's
        # output, while inputItemOutputIndex() reports the immediate item's output
        # (always 0 when the wire arrives via a dot).
        node_output_index = self._try_method(connection, "outputIndex", None)
        source_output_index = item_output_index if item_output_index is not None else node_output_index
        target_input_index = self._safe_method(connection, "inputIndex", None)
        key = "%s:%s->%s:%s" % (source_path, source_output_index, target_path, target_input_index)
        return {
            "key": key,
            "source": {
                "node": _path_of(input_node),
                "item": source_path,
                "output_index": source_output_index,
                "node_output_index": node_output_index,
                "output_name": self._try_method(connection, "inputName", None),
                "output_label": self._try_method(connection, "inputLabel", None),
                "output_data_type": self._try_method(connection, "inputDataType", None),
            },
            "target": {
                "node": _path_of(output_node),
                "item": target_path,
                "input_index": target_input_index,
                "input_name": self._try_method(connection, "outputName", None),
                "input_label": self._try_method(connection, "outputLabel", None),
                "input_data_type": self._try_method(connection, "outputDataType", None),
            },
            "subnet_indirect_input": _path_of(subnet_indirect),
            "selected": self._safe_method(connection, "isSelected", None),
            "class": connection.__class__.__name__,
        }

    def _network_item_record(self, item: Any) -> Dict[str, Any]:
        record = {
            "path": _path_of(item),
            "name": self._safe_method(item, "name", None),
            "class": item.__class__.__name__,
            "network_item_type": _enum_to_string(self._safe_method(item, "networkItemType", None)),
            "parent_path": _path_of(self._safe_method(item, "parent", None)),
            "position": _as_plain(self._safe_method(item, "position", None), self.max_text_chars),
            "size": _as_plain(self._safe_method(item, "size", None), self.max_text_chars),
            "color": _as_plain(self._safe_method(item, "color", None), self.max_text_chars),
            "comment": _as_plain(self._safe_method(item, "comment", None), self.max_text_chars),
            "selected": self._safe_method(item, "isSelected", None),
        }
        text = self._safe_method(item, "text", None)
        if text is not None:
            record["text"] = _as_plain(text, self.max_text_chars)
        item_list = self._safe_method(item, "items", None)
        if item_list is not None:
            record["items"] = [_path_of(child) for child in item_list]
        return record

    def _node_parameters(self, node: Any) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
        records = []
        code_blocks = []
        if self.include_parameter_state:
            # Houdini evaluates Hide When / Disable When rules when a Parameter
            # Pane loads a node. Explicitly refresh them so headless exports and
            # nodes not currently shown in a pane match the real UI.
            self._safe_method(node, "updateParmStates", None)
        parm_tuples = self._safe_method(node, "parmTuples", ())
        for parm_tuple in parm_tuples or ():
            template = self._safe_method(parm_tuple, "parmTemplate", None)
            if not self.include_hidden_parms and self._template_hidden(template):
                continue
            if self.changed_only and self._parm_tuple_is_at_default(parm_tuple):
                continue

            tuple_record = self._parm_tuple_record(node, parm_tuple, template)
            records.append(tuple_record)
            detected = self._detect_code_blocks(node, tuple_record)
            code_blocks.extend(detected)
        return records, code_blocks

    def _parm_tuple_record(self, node: Any, parm_tuple: Any, template: Any) -> Dict[str, Any]:
        # hou.ParmTuple is itself a sequence of hou.Parm components; it has no
        # parms() method. Iterating the tuple is what exposes value1v1, value1v2,
        # etc. and therefore their individual expressions/raw values.
        parms = self._safe(
            "%s.components" % (_path_of(parm_tuple) or "<parm_tuple>"),
            lambda: list(parm_tuple),
            [],
        )
        parm_records = [self._parm_record(parm, template) for parm in parms]
        raw_values = self._parm_tuple_raw_values(parm_records)
        values = raw_values
        values_source = "raw_input"
        evaluated_captured = False
        if self.evaluate_parameters:
            evaluated_values = _as_plain(self._safe_method(parm_tuple, "eval", None), self.max_text_chars)
            if evaluated_values is not None:
                values = evaluated_values
                values_source = "evaluated"
                evaluated_captured = True
                if len(parm_records) == 1:
                    if isinstance(evaluated_values, (list, tuple)) and len(evaluated_values) == 1:
                        component_values = [evaluated_values[0]]
                    else:
                        component_values = [evaluated_values]
                elif isinstance(evaluated_values, (list, tuple)):
                    component_values = list(evaluated_values)
                else:
                    component_values = []
                for index, parm_record in enumerate(parm_records):
                    if index < len(component_values):
                        parm_record["evaluated_value"] = component_values[index]
                        parm_record["value_evaluated"] = True
        visible_states = [parm_record.get("is_visible") for parm_record in parm_records]
        disabled_states = [parm_record.get("is_disabled") for parm_record in parm_records]
        return {
            "name": self._safe_method(parm_tuple, "name", None),
            "label": self._safe_method(parm_tuple, "description", None),
            "path": self._safe_method(parm_tuple, "path", None),
            "folders": self._parm_tuple_folders(parms),
            "template": self._parm_template_record(template),
            "is_at_default": self._parm_tuple_is_at_default(parm_tuple)
            if (self.evaluate_parameters or self.include_parameter_state or self.changed_only)
            else None,
            "is_time_dependent": self._safe_method(parm_tuple, "isTimeDependent", None) if self.include_parameter_state else None,
            "state_evaluated": self.include_parameter_state,
            "values": values,
            "raw_values": raw_values,
            "values_source": values_source,
            "values_evaluated": evaluated_captured,
            "has_expression": any(_parm_record_expression_source(parm_record) is not None for parm_record in parm_records),
            "ui_visible": any(state is True for state in visible_states)
            if any(state is not None for state in visible_states)
            else None,
            "ui_disabled": all(state is True for state in disabled_states)
            if any(state is not None for state in disabled_states)
            else None,
            "parms": parm_records,
        }

    def _parm_tuple_raw_values(self, parm_records: Sequence[Dict[str, Any]]) -> Any:
        values = []
        for parm_record in parm_records:
            value = self._parm_raw_value(parm_record)
            if value is not None:
                values.append(value)
        if not values:
            return None
        if len(values) == 1:
            return values[0]
        return values

    def _parm_raw_value(self, parm_record: Dict[str, Any]) -> Any:
        for key in ("expression", "unexpanded_string", "raw_value", "evaluated_value"):
            value = parm_record.get(key)
            if value is not None:
                return value
        return None

    def _parm_record(self, parm: Any, template: Any) -> Dict[str, Any]:
        capture_live_menu = self.include_parameter_state and self._template_has_dynamic_choice_menu(template)
        keyframes = self._safe_method(parm, "keyframes", ())
        keyframe_records = [self._keyframe_record(keyframe) for keyframe in keyframes or ()]
        raw_value = _as_plain(self._try_method(parm, "rawValue", None), self.max_text_chars)
        unexpanded_string = _as_plain(self._try_method(parm, "unexpandedString", None), self.max_text_chars)
        is_showing_expression = self._try_method(parm, "isShowingExpression", None)
        keyframe_expressions = [
            str(keyframe.get("expression"))
            for keyframe in keyframe_records
            if keyframe.get("expression") not in (None, "")
        ]
        meaningful_keyframe_expressions = [
            source for source in keyframe_expressions if not _is_trivial_expression_source(source)
        ]
        expression = _as_plain(self._try_method(parm, "expression", None), self.max_text_chars)
        if expression in (None, ""):
            # Numeric parameter expressions are stored as channel keyframes.  On
            # some parameter kinds/versions parm.expression() is unavailable,
            # while the keyframe still exposes the exact source expression.
            if meaningful_keyframe_expressions:
                # Prefer the text read from the keyframe itself. A numeric UI
                # display/evaluation value must never replace it.
                expression = (
                    raw_value
                    if raw_value in meaningful_keyframe_expressions
                    else meaningful_keyframe_expressions[0]
                )
            elif is_showing_expression and raw_value not in (None, ""):
                expression = raw_value

        keyframe_languages = list(
            dict.fromkeys(
                language
                for language in (keyframe.get("expression_language") for keyframe in keyframe_records)
                if language not in (None, "")
            )
        )
        expression_language = _enum_to_string(self._try_method(parm, "expressionLanguage", None))
        if expression_language is None and len(keyframe_languages) == 1:
            expression_language = keyframe_languages[0]

        source_text = expression if not _is_trivial_expression_source(expression) else None
        if (
            source_text in (None, "")
            and is_showing_expression
            and raw_value not in (None, "")
            and not _is_trivial_expression_source(raw_value)
        ):
            source_text = raw_value
        if (
            source_text in (None, "")
            and isinstance(unexpanded_string, str)
            and ("$" in unexpanded_string or "`" in unexpanded_string)
        ):
            source_text = unexpanded_string

        parm_path = _path_of(parm)
        referenced_parm = self._try_method(parm, "getReferencedParm", None)
        referenced_parm_path = _path_of(referenced_parm)
        if referenced_parm_path == parm_path:
            referenced_parm_path = None

        chop_override = None
        override_track = self._try_method(parm, "overrideTrack", None)
        if override_track is not None:
            chop_node = self._try_method(override_track, "chopNode", None)
            active = self._try_method(parm, "isOverrideTrackActive", None)
            if active is None:
                active = self._try_method(override_track, "isOverrideActive", None)
            override_parm = self._try_method(override_track, "overrideParm", None)
            chop_override = {
                "track_name": self._try_method(override_track, "name", None),
                "chop_node": _path_of(chop_node),
                "active": active,
                "override_parm": _path_of(override_parm),
                "num_samples": self._try_method(override_track, "numSamples", None),
            }
            chop_override = {key: value for key, value in chop_override.items() if value is not None}

        record = {
            "name": self._safe_method(parm, "name", None),
            "path": parm_path,
            "component_index": self._safe_method(parm, "componentIndex", None),
            "alias": self._try_method(parm, "alias", None),
            "raw_value": raw_value,
            "unexpanded_string": unexpanded_string,
            "evaluated_value": None,
            "value_evaluated": False,
            "expression": expression,
            "expressions": list(dict.fromkeys(keyframe_expressions)) if keyframe_records else ([expression] if expression not in (None, "") else []),
            "expression_language": expression_language,
            "expression_languages": keyframe_languages or ([expression_language] if expression_language else []),
            "expression_kind": _expression_source_kind(source_text, expression_language),
            "source_text": source_text,
            "referenced_parm": referenced_parm_path,
            "chop_override": chop_override,
            "is_showing_expression": is_showing_expression,
            "is_at_default": self._try_method(parm, "isAtDefault", None, True, True) if self.include_parameter_state else None,
            "is_disabled": self._try_method(parm, "isDisabled", None) if self.include_parameter_state else None,
            "is_hidden": self._try_method(parm, "isHidden", None) if self.include_parameter_state else None,
            "is_visible": self._try_method(parm, "isVisible", None) if self.include_parameter_state else None,
            "is_locked": self._try_method(parm, "isLocked", None) if self.include_parameter_state else None,
            "is_spare": self._try_method(parm, "isSpare", None) if self.include_parameter_state else None,
            "is_dynamic_menu": self._try_method(parm, "isDynamicMenu", None) if capture_live_menu else None,
            "menu_items": _as_plain(self._try_method(parm, "menuItems", None), self.max_text_chars)
            if capture_live_menu
            else None,
            "menu_labels": _as_plain(self._try_method(parm, "menuLabels", None), self.max_text_chars)
            if capture_live_menu
            else None,
            "is_time_dependent": self._try_method(parm, "isTimeDependent", None) if self.include_parameter_state else None,
            "state_evaluated": self.include_parameter_state,
            "is_multi_parm_instance": self._try_method(parm, "isMultiParmInstance", None),
            "multi_parm_indices": _as_plain(self._try_method(parm, "multiParmInstanceIndices", None), self.max_text_chars),
            "containing_folders": _as_plain(self._try_method(parm, "containingFolders", ()), self.max_text_chars),
            "keyframes": keyframe_records,
        }
        parent_multi = self._try_method(parm, "parentMultiParm", None)
        if parent_multi is not None:
            record["parent_multi_parm"] = self._try_method(parent_multi, "path", None)
        return record

    def _template_has_dynamic_choice_menu(self, template: Any) -> bool:
        """Avoid running expensive attribute/preset helper menus as choices."""
        if template is None:
            return False
        template_class = template.__class__.__name__
        if template_class == "StringParmTemplate":
            menu_type = str(_enum_to_string(self._try_method(template, "menuType", None)) or "").lower()
            if "stringtoggle" in menu_type or "stringreplace" in menu_type:
                return False
        if template_class not in ("MenuParmTemplate", "IntParmTemplate", "StringParmTemplate"):
            return False
        return bool(self._try_method(template, "itemGeneratorScript", ""))

    def _keyframe_record(self, keyframe: Any) -> Dict[str, Any]:
        json_data = _as_plain(
            self._try_method(keyframe, "asJSON", None, False, True),
            self.max_text_chars,
        )
        expression = _as_plain(self._try_method(keyframe, "expression", None), self.max_text_chars)
        expression_language = _enum_to_string(self._try_method(keyframe, "expressionLanguage", None))
        if isinstance(json_data, dict):
            if expression in (None, ""):
                expression = json_data.get("expression") or json_data.get("expr")
            if expression_language is None:
                expression_language = _enum_to_string(
                    json_data.get("expression_language") or json_data.get("language")
                )
        record = {
            "class": keyframe.__class__.__name__,
            "frame": self._try_method(keyframe, "frame", None),
            "time": self._try_method(keyframe, "time", None),
            "value": _as_plain(self._try_method(keyframe, "value", None), self.max_text_chars),
            "expression": expression,
            "expression_language": expression_language,
            "expression_kind": _expression_source_kind(expression, expression_language),
            "is_expression_set": self._try_method(keyframe, "isExpressionSet", None),
            "is_expression_language_set": self._try_method(keyframe, "isExpressionLanguageSet", None),
            "slope": _as_plain(self._try_method(keyframe, "slope", None), self.max_text_chars),
            "accel": _as_plain(self._try_method(keyframe, "accel", None), self.max_text_chars),
            "in_slope": _as_plain(self._try_method(keyframe, "inSlope", None), self.max_text_chars),
            "out_slope": _as_plain(self._try_method(keyframe, "outSlope", None), self.max_text_chars),
        }
        if json_data is not None:
            # Preserve Houdini's complete keyframe serialization too. This
            # carries key-type-specific fields that differ between numeric,
            # string, and future keyframe classes.
            record["data"] = json_data
        return record

    def _parm_template_record(self, template: Any) -> Dict[str, Any]:
        if template is None:
            return {}
        fields = {
            "class": template.__class__.__name__,
            "name": self._try_method(template, "name", None),
            "label": self._try_method(template, "label", None),
            "type": _enum_to_string(self._try_method(template, "type", None)),
            "data_type": _enum_to_string(self._try_method(template, "dataType", None)),
            "string_type": _enum_to_string(self._try_method(template, "stringType", None)),
            "menu_type": _enum_to_string(self._try_method(template, "menuType", None)),
            "folder_type": _enum_to_string(self._try_method(template, "folderType", None)),
            "naming_scheme": _enum_to_string(self._try_method(template, "namingScheme", None)),
            "num_components": self._try_method(template, "numComponents", None),
            "component_labels": _as_plain(self._try_method(template, "componentLabels", None), self.max_text_chars),
            "min_value": _as_plain(self._try_method(template, "minValue", None), self.max_text_chars),
            "max_value": _as_plain(self._try_method(template, "maxValue", None), self.max_text_chars),
            "min_is_strict": self._try_method(template, "minIsStrict", None),
            "max_is_strict": self._try_method(template, "maxIsStrict", None),
            "menu_items": _as_plain(self._try_method(template, "menuItems", None), self.max_text_chars),
            "menu_labels": _as_plain(self._try_method(template, "menuLabels", None), self.max_text_chars),
            "item_generator_script": _as_plain(self._try_method(template, "itemGeneratorScript", None), self.max_text_chars),
            "item_generator_script_language": _enum_to_string(self._try_method(template, "itemGeneratorScriptLanguage", None)),
            "script_callback": _as_plain(self._try_method(template, "scriptCallback", None), self.max_text_chars),
            "script_callback_language": _enum_to_string(self._try_method(template, "scriptCallbackLanguage", None)),
            "help": _as_plain(self._try_method(template, "help", None), self.max_text_chars),
            "tags": _as_plain(self._try_method(template, "tags", None), self.max_text_chars),
            "conditionals": _as_plain(self._try_method(template, "conditionals", None), self.max_text_chars),
            "is_hidden": self._try_method(template, "isHidden", None),
            "is_disabled": self._try_method(template, "isDisabled", None),
            "join_with_next": self._try_method(template, "joinsWithNext", None),
            "is_label_hidden": self._try_method(template, "isLabelHidden", None),
            "look": _enum_to_string(self._try_method(template, "look", None)),
            "default_value": _as_plain(self._try_method(template, "defaultValue", None), self.max_text_chars),
            "default_expression": _as_plain(self._try_method(template, "defaultExpression", None), self.max_text_chars),
            "default_expression_language": _as_plain(
                self._try_method(template, "defaultExpressionLanguage", None),
                self.max_text_chars,
            ),
        }
        return {key: value for key, value in fields.items() if value is not None}

    def _template_hidden(self, template: Any) -> bool:
        if template is None:
            return False
        return bool(self._try_method(template, "isHidden", False))

    def _parm_tuple_is_at_default(self, parm_tuple: Any) -> bool:
        # compare_expressions=True is essential: the HOM default compares only
        # evaluated values, so an expression evaluating to 0/1 can otherwise be
        # incorrectly treated as an unchanged default and omitted in compact mode.
        value = self._try_method(parm_tuple, "isAtDefault", None, True, True)
        if value is None:
            value = self._safe_method(parm_tuple, "isAtDefault", None)
        if value is None:
            return False
        return bool(value)

    def _parm_tuple_folders(self, parms: Sequence[Any]) -> List[str]:
        for parm in parms:
            folders = self._try_method(parm, "containingFolders", ())
            if folders:
                return list(folders)
        return []

    def _detect_code_blocks(self, node: Any, tuple_record: Dict[str, Any]) -> List[Dict[str, Any]]:
        blocks = []
        tuple_name = str(tuple_record.get("name") or "").lower()
        label = str(tuple_record.get("label") or "").lower()
        template = tuple_record.get("template", {})
        template_class = str(template.get("class") or "")
        # Executable snippets are stored in string parameters. Numeric channel
        # expressions such as ch("../foo") are parameter sources, not code
        # blocks, even though their text happens to look like a function call.
        if template_class and "StringParmTemplate" not in template_class:
            return blocks
        if template.get("menu_items") or template.get("menu_labels"):
            # Script-language selectors contain values such as "hscript" or
            # "python" but are not themselves executable script bodies.
            return blocks

        # ParmTemplate tags frequently contain callback metadata on ordinary
        # HDA controls. Treating the whole tags dictionary as a name hint turns
        # most of an HDA interface into false-positive "Code params".
        name_says_code = any(hint in tuple_name or hint in label for hint in CODE_NAME_HINTS)
        for parm in tuple_record.get("parms", []):
            text = self._best_parm_text(parm)
            if not text:
                continue
            if parm.get("expression") not in (None, "") or parm.get("keyframes"):
                # These are already emitted losslessly as Channel source /
                # Keyframe records. Do not duplicate them as executable code.
                continue
            text_says_code = _text_looks_like_code(text)
            if name_says_code or text_says_code:
                blocks.append(
                    {
                        "node_path": _path_of(node),
                        "node_type": self._safe_method(self._safe_method(node, "type", None), "nameWithCategory", None),
                        "parm_path": parm.get("path"),
                        "parm_name": parm.get("name"),
                        "tuple_name": tuple_record.get("name"),
                        "label": tuple_record.get("label"),
                        "language_guess": self._guess_code_language(node, tuple_record, text),
                        "text": _maybe_long_text_record(text, self.max_text_chars),
                    }
                )
        return blocks

    def _best_parm_text(self, parm_record: Dict[str, Any]) -> str:
        for key in ("unexpanded_string", "raw_value", "expression", "evaluated_value"):
            value = parm_record.get(key)
            if isinstance(value, str) and value:
                return value
        return ""

    def _guess_code_language(self, node: Any, tuple_record: Dict[str, Any], text: str) -> str:
        type_name = str(self._safe_method(self._safe_method(node, "type", None), "nameWithCategory", "") or "").lower()
        name_label = (str(tuple_record.get("name") or "") + " " + str(tuple_record.get("label") or "")).lower()
        haystack = type_name + " " + name_label + " " + text[:512].lower()
        if "python" in haystack or "hou." in haystack or re.search(r"\bdef\s+\w+\s*\(", text):
            return "python"
        if "osl" in haystack:
            return "c"
        if "vex" in haystack or "wrangle" in haystack or "snippet" in haystack or "@" in text:
            return "c"
        if "hscript" in haystack or "$F" in text or "`" in text:
            return "hscript"
        return "text"

    def _capture_hda_definition(self, node: Any) -> Optional[str]:
        node_type = self._safe_method(node, "type", None)
        definition = self._safe_method(node_type, "definition", None) if node_type is not None else None
        if definition is None:
            return None

        category = self._safe_method(self._safe_method(node_type, "category", None), "name", None)
        node_type_name = self._safe_method(node_type, "name", None)
        library_path = self._safe_method(definition, "libraryFilePath", None)
        key = "%s/%s" % (category, node_type_name)
        if self.include_scene_paths:
            key = "%s@%s" % (key, library_path)
        if key in self._definition_keys:
            return key

        self._definition_keys.add(key)
        record = {
            "key": key,
            "node_type": node_type_name,
            "node_type_with_category": self._safe_method(node_type, "nameWithCategory", None),
            "category": category,
            "description": self._safe_method(definition, "description", None),
            "version": self._safe_method(definition, "version", None),
            "comment": self._safe_method(definition, "comment", None),
            "icon": self._safe_method(definition, "icon", None),
            "is_current": self._safe_method(definition, "isCurrent", None),
            "is_preferred": self._safe_method(definition, "isPreferred", None),
            "modification_time": self._safe_method(definition, "modificationTime", None),
            "extra_info": _as_plain(self._safe_method(definition, "extraInfo", None), self.max_text_chars),
            "extra_file_options": _as_plain(self._safe_method(definition, "extraFileOptions", None), self.max_text_chars),
            "sections_included": self._should_include_hda_sections(library_path),
            "sections": [],
        }
        if self.include_scene_paths:
            record["library_file_path"] = library_path
        if record["sections_included"]:
            sections = self._safe_method(definition, "sections", {})
            for section_name in sorted((sections or {}).keys()):
                section = sections[section_name]
                record["sections"].append(self._hda_section_record(section))
        else:
            if self.hda_section_mode != "none":
                sections = self._safe_method(definition, "sections", {})
                record["section_names"] = sorted((sections or {}).keys())
            record["sections_skipped_reason"] = self._hda_skip_reason(library_path)
        self._hda_definitions.append(record)
        return key

    def _should_include_hda_sections(self, library_path: Optional[str]) -> bool:
        if self.hda_section_mode == "none":
            return False
        if self.hda_section_mode == "all":
            return True
        if not library_path:
            return False
        if library_path == "Embedded":
            return True
        try:
            hfs = hou.getenv("HFS")
        except Exception:
            hfs = None
        if hfs and os.path.abspath(str(library_path)).lower().startswith(os.path.abspath(str(hfs)).lower()):
            return False
        return True

    def _hda_skip_reason(self, library_path: Optional[str]) -> str:
        if self.hda_section_mode == "none":
            return "hda_section_mode=none"
        return "SideFX/built-in library sections skipped in scene mode; use --hda-section-mode all to include them"

    def _hda_section_record(self, section: Any) -> Dict[str, Any]:
        name = self._safe_method(section, "name", None)
        size = self._safe_method(section, "size", None)
        record = {
            "name": name,
            "size": size,
            "modification_time": self._safe_method(section, "modificationTime", None),
        }
        data = self._safe_method(section, "binaryContents", None)
        if isinstance(data, bytes):
            record["sha256"] = _sha256_bytes(data)
            record["is_probably_text"] = _is_probably_text(data)
            if record["is_probably_text"]:
                try:
                    text = data.decode("utf-8")
                except UnicodeDecodeError:
                    text = data.decode("latin-1", errors="replace")
                record["contents"] = _maybe_long_text_record(text, self.max_text_chars)
            else:
                record["contents"] = {
                    "text": None,
                    "note": "binary section omitted",
                    "length": len(data),
                    "sha256": record["sha256"],
                }
        else:
            text = self._safe_method(section, "contents", None)
            if isinstance(text, str):
                record["sha256"] = _sha256_text(text)
                record["is_probably_text"] = True
                record["contents"] = _maybe_long_text_record(text, self.max_text_chars)
        return record

    def _geometry_summary(self, node: Any) -> Optional[Dict[str, Any]]:
        geometry = self._node_geometry(node)
        if geometry is None:
            return None
        primitive_samples = self._sample_geometry_elements(geometry, "iterPrims", "prims")
        vertices = self._sample_vertices_from_prims(primitive_samples, self.geometry_sample_count)
        attributes: Dict[str, List[Dict[str, Any]]] = {}
        omitted_attributes: Dict[str, List[Dict[str, Any]]] = {}
        for owner, method_name in (
            ("primitive", "primAttribs"),
            ("global", "globalAttribs"),
            ("point", "pointAttribs"),
            ("vertex", "vertexAttribs"),
        ):
            records, omitted = self._attribute_records(geometry, method_name, owner, primitive_samples)
            attributes[owner] = records
            omitted_attributes[owner] = omitted
        return {
            "is_valid": self._try_method(geometry, "isValid", None),
            "mode": {
                "node_mode": self.geometry_node_mode,
                "sample_count": self.geometry_sample_count,
                "standard_attributes_included": self.include_standard_attributes,
                "private_attributes_included": self.include_private_attributes,
            },
            "counts": self._geometry_counts(geometry),
            "attribute_counts": {owner: len(records) for owner, records in attributes.items()},
            "attributes": attributes,
            "omitted_standard_attributes": omitted_attributes,
            "sample_vertices": vertices,
            "groups": {
                "point": self._group_records(geometry, "pointGroups"),
                "primitive": self._group_records(geometry, "primGroups"),
                "vertex": self._group_records(geometry, "vertexGroups"),
                "edge": self._group_records(geometry, "edgeGroups"),
            },
        }

    def _attribute_scopes(self) -> List[Tuple[str, Any]]:
        scopes: List[Tuple[str, Any]] = []
        attrib_scope = getattr(hou, "attribScope", None)
        public_scope = getattr(attrib_scope, "Public", None) if attrib_scope is not None else None
        private_scope = getattr(attrib_scope, "Private", None) if attrib_scope is not None else None
        if public_scope is not None:
            scopes.append(("public", public_scope))
        else:
            scopes.append(("default", None))
        if self.include_private_attributes and private_scope is not None:
            scopes.append(("private", private_scope))
        return scopes

    def _attribute_records(
        self,
        geometry: Any,
        method_name: str,
        owner: str,
        primitive_samples: Sequence[Any],
    ) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
        records: List[Dict[str, Any]] = []
        omitted: List[Dict[str, Any]] = []
        seen: set = set()
        method = _method(geometry, method_name)
        if method is None:
            return records, omitted
        sample_elements = self._attribute_sample_elements(geometry, owner, primitive_samples)
        for scope_name, scope in self._attribute_scopes():
            try:
                attribs = method(scope) if scope is not None else method()
            except Exception:
                if scope is None or scope_name == "public":
                    attribs = self._try_method(geometry, method_name, ())
                else:
                    attribs = ()
            for attrib in attribs or ():
                name = self._try_method(attrib, "name", "")
                key = (owner, scope_name, name)
                if key in seen:
                    continue
                seen.add(key)
                if self._is_standard_attribute(owner, attrib):
                    omitted.append(self._omitted_attribute_record(attrib, owner, scope_name, "standard_attribute"))
                    continue
                records.append(self._attribute_record(geometry, attrib, owner, scope_name, sample_elements))
        records.sort(key=lambda row: (str(row.get("scope", "")), str(row.get("name", ""))))
        omitted.sort(key=lambda row: (str(row.get("scope", "")), str(row.get("name", ""))))
        return records, omitted

    def _attribute_sample_elements(self, geometry: Any, owner: str, primitive_samples: Sequence[Any]) -> Sequence[Any]:
        if self.geometry_sample_count == 0:
            return ()
        if owner == "point":
            return self._sample_geometry_elements(geometry, "iterPoints", "points")
        if owner in ("primitive", "vertex"):
            return primitive_samples
        return ()

    def _is_standard_attribute(self, owner: str, attrib: Any) -> bool:
        if self.include_standard_attributes:
            return False
        name = str(self._try_method(attrib, "name", "") or "").lower()
        return name in STANDARD_ATTRIBUTE_NAMES_BY_OWNER.get(owner, set())

    def _omitted_attribute_record(self, attrib: Any, owner: str, scope_name: str, reason: str) -> Dict[str, Any]:
        return {
            "name": self._try_method(attrib, "name", None),
            "owner": owner,
            "scope": scope_name,
            "reason": reason,
            "data_type": _enum_to_string(self._try_method(attrib, "dataType", None)),
            "size": self._try_method(attrib, "size", None),
        }

    def _attribute_record(self, geometry: Any, attrib: Any, owner: str, scope_name: str, elements: Sequence[Any]) -> Dict[str, Any]:
        string_count = self._try_method(attrib, "stringCount", 0)
        dict_count = self._try_method(attrib, "dictCount", 0)
        samples = self._attribute_sample_values(geometry, attrib, owner, elements)
        record = {
            "name": self._try_method(attrib, "name", None),
            "owner": owner,
            "scope": scope_name,
            "type": _enum_to_string(self._try_method(attrib, "type", None)),
            "data_type": _enum_to_string(self._try_method(attrib, "dataType", None)),
            "numeric_data_type": _enum_to_string(self._try_method(attrib, "numericDataType", None)),
            "is_array": self._try_method(attrib, "isArrayType", None),
            "size": self._try_method(attrib, "size", None),
            "qualifier": self._try_method(attrib, "qualifier", None),
            "default_value": _as_plain(self._try_method(attrib, "defaultValue", None), self.max_text_chars),
            "is_transformed_as_normal": self._try_method(attrib, "isTransformedAsNormal", None),
            "options": _as_plain(self._try_method(attrib, "options", None), self.max_text_chars),
            "data_id": self._try_method(attrib, "dataId", None),
            "string_table": self._attribute_table_record(attrib, "strings", string_count),
            "dict_table": self._attribute_table_record(attrib, "dicts", dict_count),
        }
        index_pair_tables = self._try_method(attrib, "indexPairPropertyTables", ())
        if index_pair_tables:
            record["index_pair_property_tables"] = _as_plain(index_pair_tables, self.max_text_chars)
        if samples:
            record["sample_values"] = samples
        return {key: value for key, value in record.items() if value is not None}

    def _attribute_table_record(self, attrib: Any, method_name: str, count: int) -> Dict[str, Any]:
        sample: List[Any] = []
        if self.geometry_sample_count != 0 and count:
            values = self._try_method(attrib, method_name, ())
            sample = self._sample_items(values)
        return {
            "count": count,
            "sample_values": _as_plain(sample, self.max_text_chars),
            "sample_truncated": self._sample_is_truncated(count),
        }

    def _attribute_sample_values(self, geometry: Any, attrib: Any, owner: str, elements: Sequence[Any]) -> List[Dict[str, Any]]:
        if self.geometry_sample_count == 0:
            return []
        if owner == "global":
            value = self._try_method(geometry, "attribValue", None, attrib)
            if value is None:
                # Some attrib kinds only resolve by name (and dict attribs need dictValue).
                name = self._try_method(attrib, "name", None)
                if name:
                    value = self._try_method(geometry, "attribValue", None, name)
                    if value is None:
                        value = self._try_method(geometry, "dictValue", None, name)
            return [{"value": _as_plain(value, self.max_text_chars)}]
        if owner == "vertex":
            return self._vertex_attribute_sample_values(attrib, elements)
        samples = []
        for index, element in enumerate(self._sample_items(elements)):
            samples.append(
                {
                    "index": index,
                    "number": self._try_method(element, "number", index),
                    "value": _as_plain(self._try_method(element, "attribValue", None, attrib), self.max_text_chars),
                }
            )
        return samples

    def _vertex_attribute_sample_values(self, attrib: Any, prims: Sequence[Any]) -> List[Dict[str, Any]]:
        samples = []
        if self.geometry_sample_count == 0:
            return samples
        for prim in prims or ():
            prim_number = self._try_method(prim, "number", None)
            for vertex in self._try_method(prim, "vertices", ()) or ():
                samples.append(
                    {
                        "index": len(samples),
                        "prim_number": prim_number,
                        "vertex_number": self._try_method(vertex, "number", None),
                        "linear_number": self._try_method(vertex, "linearNumber", None),
                        "point_number": self._try_method(self._try_method(vertex, "point", None), "number", None),
                        "value": _as_plain(self._try_method(vertex, "attribValue", None, attrib), self.max_text_chars),
                    }
                )
                if self._sample_limit_reached(len(samples)):
                    return samples
        return samples

    def _sample_vertices_from_prims(self, prims: Sequence[Any], limit: int) -> List[Dict[str, Any]]:
        samples = []
        if limit == 0:
            return samples
        for prim in prims or ():
            prim_number = self._try_method(prim, "number", None)
            for vertex in self._try_method(prim, "vertices", ()) or ():
                samples.append(
                    {
                        "prim_number": prim_number,
                        "vertex_number": self._try_method(vertex, "number", None),
                        "linear_number": self._try_method(vertex, "linearNumber", None),
                        "point_number": self._try_method(self._try_method(vertex, "point", None), "number", None),
                    }
                )
                if limit > 0 and len(samples) >= limit:
                    return samples
        return samples

    def _geometry_counts(self, geometry: Any) -> Dict[str, Any]:
        point_count = self._geometry_intrinsic(geometry, "pointcount")
        primitive_count = self._geometry_intrinsic(geometry, "primitivecount")
        vertex_count = self._geometry_intrinsic(geometry, "vertexcount")
        return {
            "points": point_count,
            "vertices": vertex_count,
            "primitives": primitive_count,
        }

    def _geometry_intrinsic(self, geometry: Any, name: str) -> Any:
        value = self._try_method(geometry, "intrinsicValue", None, name)
        if value is not None:
            return value
        return self._try_method(geometry, name, None)

    def _sample_geometry_elements(self, geometry: Any, iter_method_name: str, all_method_name: str) -> List[Any]:
        if self.geometry_sample_count == 0:
            return []
        if self.geometry_sample_count < 0:
            return list(self._try_method(geometry, all_method_name, ()) or ())
        iterator = self._try_method(geometry, iter_method_name, None)
        if iterator is None:
            iterator = iter(self._try_method(geometry, all_method_name, ()) or ())
        return self._take_from_iterable(iterator, self.geometry_sample_count)

    def _sample_items(self, values: Sequence[Any]) -> List[Any]:
        if self.geometry_sample_count < 0:
            return list(values or ())
        if self.geometry_sample_count == 0:
            return []
        return self._take_from_iterable(values or (), self.geometry_sample_count)

    def _take_from_iterable(self, values: Iterable[Any], limit: int) -> List[Any]:
        items = []
        for value in values:
            items.append(value)
            if len(items) >= limit:
                break
        return items

    def _sample_limit_reached(self, sample_len: int) -> bool:
        return self.geometry_sample_count > 0 and sample_len >= self.geometry_sample_count

    def _sample_is_truncated(self, total_count: int) -> bool:
        try:
            count = int(total_count or 0)
        except Exception:
            return False
        return self.geometry_sample_count >= 0 and count > self.geometry_sample_count

    def _group_records(self, geometry: Any, method_name: str) -> List[Dict[str, Any]]:
        groups = self._try_method(geometry, method_name, ())
        records = []
        for group in groups or ():
            count = self._try_method(group, "size", None)
            if count is None:
                # Older hou.Group classes have no size(); count the members instead.
                for items_method in ("points", "prims", "vertices", "edges"):
                    items = self._try_method(group, items_method, None)
                    if items is not None:
                        try:
                            count = len(items)
                        except Exception:
                            count = None
                        break
            records.append(
                {
                    "name": self._try_method(group, "name", None),
                    "count": count,
                    "is_ordered": self._try_method(group, "isOrdered", None),
                    "scope": _enum_to_string(self._try_method(group, "scope", None)),
                    "type": group.__class__.__name__,
                }
            )
        return records


def _houdini_version_suffix(data: Dict[str, Any]) -> str:
    version = (data.get("scene", {}) or {}).get("houdini_version")
    if not version:
        return ""
    return " (Houdini %s)" % version


def _llm_footer_lines(data: Dict[str, Any]) -> List[str]:
    version = (data.get("scene", {}) or {}).get("houdini_version")
    label = "Houdini %s" % version if version else "Houdini"
    if (data.get("options", {}) or {}).get("markdown_mode") in ("smart", "rbd_smart"):
        omission_rule = (
            "Smart セクションで記載のない現在有効な UI 設定は Houdini のデフォルト値です。"
            "非表示の内部パラメータは意図的に対象外であり、その値を推測しないでください。"
        )
    else:
        omission_rule = "それ以外の記載のないパラメータは Houdini のデフォルト値とみなしてください。"
    return [
        "",
        "---",
        "",
        "**更新について:** %s" % EXPORT_FRESHNESS_NOTICE_JA,
        "",
        "**アシスタントへ:** 上記はユーザーの現在の %s ネットワークのスナップショットです。"
        "回答は必ずこのダンプに基づいてください。Path base がある場合は相対見出しをそこへ連結して正確なノードパスとして参照し、"
        "記載された値を現在の状態として扱ってください。`... +N more` があるノードの省略分は不明であり、"
        "デフォルト値とはみなさないでください。%s"
        "接続に沿ってデータフローを追い、ノードの仕様に少しでも不確かさがあれば SideFX の最新公式ドキュメントを調べ、"
        "正しい Houdini / VEX の知識に基づいて分析してください。"
        "このダンプに無い情報は推測せず「不明」と答えてください。" % (label, omission_rule),
    ]


def _render_packed_rig_tree(record: Any, indent: str = "") -> List[str]:
    if not isinstance(record, dict):
        return []
    raw_paths = record.get("paths", []) or []
    paths = sorted({str(path) for path in raw_paths if str(path or "").strip()})
    if not paths:
        return []
    folders = {str(path) for path in record.get("folders", []) or []}

    tree: Dict[str, Any] = {}
    for path in paths:
        cursor = tree
        for component in [part for part in path.strip("/").split("/") if part]:
            cursor = cursor.setdefault(component, {})

    lines = [indent + "- Packed rig tree:", indent + "  - `/`"]

    def emit(children: Dict[str, Any], parent_path: str, depth: int) -> None:
        for name in sorted(children):
            child_path = (parent_path.rstrip("/") + "/" + name) if parent_path != "/" else "/" + name
            grandchildren = children[name]
            is_folder = bool(grandchildren) or child_path in folders
            suffix = "/" if is_folder else ""
            lines.append(indent + "  " * depth + "- `%s%s`" % (name, suffix))
            emit(grandchildren, child_path, depth + 1)

    emit(tree, "/", 2)
    return lines


# Node-type importance for ordering the per-node sections. LLM attention is
# strongest at the start and end of long context, so high-signal nodes
# (solvers, wrangles, fracture setups) go to both ends and plumbing/primitive
# nodes (box, merge, transform, ...) sink to the middle.
_COMPACT_TYPE_IMPORTANCE = (
    (100, ("solver", "dopnet", "dopimport", "simulation")),
    (90, ("wrangle", "python", "opencl", "vopnet", "attribvop", "snippet")),
    (75, ("fracture", "constraint", "configure", "vellum", "pyro", "flip", "popnet", "boolean")),
    (60, ("filecache", "rop_", "cache", "bake", "output")),
    (50, ("copytopoints", "copy", "scatter", "foreach", "block_begin", "block_end", "switch")),
    (10, (
        "merge", "null", "name", "transform", "xform", "unpack", "pack",
        "box", "sphere", "grid", "tube", "line", "circle", "platonic", "font",
        "blast", "clip", "delete", "group",
    )),
)


def _compact_node_importance(node: Dict[str, Any]) -> int:
    node_type = node.get("type", {}) or {}
    type_text = _node_type_token(node_type.get("name_with_category") or node_type.get("name"))
    score = 30
    for tier_score, keywords in _COMPACT_TYPE_IMPORTANCE:
        if any(keyword in type_text for keyword in keywords):
            score = tier_score
            break
    if node.get("code_blocks"):
        score = max(score, 85)
    flags = node.get("flags", {}) or {}
    if flags.get("isDisplayFlagSet") is True or flags.get("isRenderFlagSet") is True:
        score += 8
    changed = sum(
        1
        for parm_tuple in node.get("parameters", []) or []
        if parm_tuple.get("is_at_default") is False or _parameter_tuple_expression_value(parm_tuple)[0]
    )
    score += min(changed, 10)
    if node.get("comment"):
        score += 5
    return score


# Nodes at or above this importance score also list their leading default
# parameters, so e.g. a solver left entirely at defaults still shows its core
# settings (Houdini puts the most relevant parameters first in the interface).
COMPACT_IMPORTANT_SCORE = 70
DEFAULT_COMPACT_IMPORTANT_PARAM_FLOOR = 10
_COMPACT_DEFAULT_INTERNAL_NAMES = {"generatedcode"}
_COMPACT_DEFAULT_INTERNAL_PREFIXES = ("vex_", "bind")


def _compact_default_parameter_chunks(
    parameters: Sequence[Dict[str, Any]],
    limit: int,
    max_per_line: int = 6,
) -> List[str]:
    if limit <= 0:
        return []
    ramp_names = {
        str(parm_tuple.get("name"))
        for parm_tuple in parameters
        if (parm_tuple.get("template", {}) or {}).get("class") == "RampParmTemplate"
    }
    entries: List[str] = []
    for parm_tuple in parameters:
        if parm_tuple.get("is_at_default") is not True or _parameter_tuple_expression_value(parm_tuple)[0]:
            continue
        template = parm_tuple.get("template", {}) or {}
        if template.get("class") in _ULTRA_UI_NOISE_TEMPLATE_CLASSES:
            continue
        if template.get("class") == "RampParmTemplate" or _compact_folder_is_noise(template):
            continue
        name = str(parm_tuple.get("name") or "")
        if name in _COMPACT_DEFAULT_INTERNAL_NAMES or name.startswith(_COMPACT_DEFAULT_INTERNAL_PREFIXES):
            continue
        if ramp_names:
            match = _RAMP_INSTANCE_PATTERN.match(name)
            if match and match.group("base") in ramp_names:
                continue
        entry = _compact_parameter_entry(parm_tuple)
        if entry:
            entries.append(entry)
        if len(entries) >= limit:
            break
    chunks = []
    for index in range(0, len(entries), max_per_line):
        chunks.append("; ".join(entries[index : index + max_per_line]))
    return chunks


def _attention_ordered_nodes(nodes: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Order nodes so importance is highest at the start and end, lowest in the middle."""
    ranked = sorted(nodes, key=lambda node: (-_compact_node_importance(node), str(node.get("path", ""))))
    front: List[Dict[str, Any]] = []
    back: List[Dict[str, Any]] = []
    for index, node in enumerate(ranked):
        if index % 2 == 0:
            front.append(node)
        else:
            back.append(node)
    return front + list(reversed(back))


def _compact_inspector_path_base(nodes: Sequence[Dict[str, Any]]) -> Optional[str]:
    parent_parts = []
    for node in nodes:
        path = str(node.get("path") or "")
        parts = [part for part in path.strip("/").split("/") if part]
        if len(parts) > 1:
            parent_parts.append(parts[:-1])
    if not parent_parts:
        return None
    common = list(parent_parts[0])
    for parts in parent_parts[1:]:
        common = common[: min(len(common), len(parts))]
        for index, (left, right) in enumerate(zip(common, parts)):
            if left != right:
                common = common[:index]
                break
        if not common:
            return None
    return "/" + "/".join(common) if common else None


def _compact_path_relative_to_base(path: Any, base: Optional[str]) -> str:
    text = str(path or "?")
    if base and text.startswith(base.rstrip("/") + "/"):
        return text[len(base.rstrip("/") + "/") :]
    return text


def _smart_is_rbd_node(node: Dict[str, Any]) -> bool:
    node_type = node.get("type", {}) or {}
    category = _node_type_token(node_type.get("category"))
    name_with_category = str(node_type.get("name_with_category") or "").strip().lower()
    if category != "sop" and not name_with_category.startswith("sop/"):
        return False
    type_name = _node_type_token(node_type.get("name_with_category") or node_type.get("name"))
    return type_name.startswith("rbd")


def _smart_menu_data(parm_tuple: Dict[str, Any]) -> Tuple[List[Any], List[Any]]:
    template = parm_tuple.get("template", {}) or {}
    items = list(template.get("menu_items") or [])
    labels = list(template.get("menu_labels") or [])
    for parm in parm_tuple.get("parms", []) or []:
        live_items = parm.get("menu_items") or []
        live_labels = parm.get("menu_labels") or []
        if live_items or live_labels:
            return list(live_items), list(live_labels)
    return items, labels


def _smart_is_menu(parm_tuple: Dict[str, Any]) -> bool:
    template = parm_tuple.get("template", {}) or {}
    menu_type = str(template.get("menu_type") or "").lower()
    if template.get("class") == "StringParmTemplate" and (
        "stringtoggle" in menu_type or "stringreplace" in menu_type
    ):
        # These are editable text/pattern fields with a helper menu, not a
        # single-choice UI. Their current text must not be replaced by one of
        # the helper entries.
        return False
    items, labels = _smart_menu_data(parm_tuple)
    return bool(items or labels)


def _smart_is_value_parameter(parm_tuple: Dict[str, Any]) -> bool:
    template = parm_tuple.get("template", {}) or {}
    template_class = str(template.get("class") or "")
    if template_class in _ULTRA_UI_NOISE_TEMPLATE_CLASSES:
        return False
    if _compact_folder_is_noise(template):
        return False
    if template.get("is_hidden") is True:
        return False
    if parm_tuple.get("ui_visible") is False and template_class != "RampParmTemplate":
        # A hou.Ramp container itself reports invisible; its visible multiparm
        # children are the actual ramp editor. Keep the container so those
        # children can be collapsed back into one UI row.
        return False
    return bool(parm_tuple.get("label") or template.get("label"))


def _smart_ramp_state(
    parameters: Sequence[Dict[str, Any]],
) -> Tuple[set, Dict[str, str], set]:
    ramp_names = {
        str(parm_tuple.get("name"))
        for parm_tuple in parameters
        if (parm_tuple.get("template", {}) or {}).get("class") == "RampParmTemplate"
    }
    instance_names: set = set()
    instances_by_ramp: Dict[str, Dict[int, Dict[str, Any]]] = {}
    changed_ramps: set = set()
    for parm_tuple in parameters:
        name = str(parm_tuple.get("name") or "")
        if name in ramp_names:
            if parm_tuple.get("is_at_default") is False or _parameter_tuple_expression_value(parm_tuple)[0]:
                changed_ramps.add(name)
            continue
        match = _RAMP_INSTANCE_PATTERN.match(name)
        if not match or match.group("base") not in ramp_names:
            continue
        instance_names.add(name)
        base = match.group("base")
        channel = match.group("channel")
        slot = instances_by_ramp.setdefault(base, {}).setdefault(int(match.group("index")), {})
        if channel == "interp":
            menu_label = _compact_menu_value_label(parm_tuple, _compact_parameter_scalar(parm_tuple))
            slot[channel] = menu_label if menu_label is not None else _compact_parameter_scalar(parm_tuple)
        else:
            slot[channel] = _compact_parameter_scalar(parm_tuple)
        if parm_tuple.get("is_at_default") is False or _parameter_tuple_expression_value(parm_tuple)[0]:
            changed_ramps.add(base)

    summaries = {
        name: summary
        for name, summary in (
            (name, _compact_ramp_summary(instances_by_ramp.get(name, {}))) for name in ramp_names
        )
        if summary
    }
    return instance_names, summaries, changed_ramps


def _smart_selected_parameters(
    parameters: Sequence[Dict[str, Any]],
    minimum_rows: int = 0,
) -> List[Dict[str, Any]]:
    """Keep effective UI settings without recreating every default widget."""
    selected: List[Dict[str, Any]] = []
    leading_defaults: List[Dict[str, Any]] = []
    ramp_instance_names, _ramp_summaries, changed_ramps = _smart_ramp_state(parameters)
    for parm_tuple in parameters:
        if not _smart_is_value_parameter(parm_tuple):
            continue
        name = str(parm_tuple.get("name") or "")
        if name in ramp_instance_names:
            continue
        template = parm_tuple.get("template", {}) or {}
        has_expression = _parameter_tuple_expression_value(parm_tuple)[0]
        default_state = parm_tuple.get("is_at_default")
        changed = (
            default_state is False
            or (default_state is None and has_expression)
            or name in changed_ramps
        )
        disabled = parm_tuple.get("ui_disabled") is True

        # A disabled default does not affect the current result. A disabled
        # edited value is retained so the LLM can see the value waiting behind
        # the current UI switch, and it is explicitly marked as disabled.
        if disabled and not changed:
            continue
        if changed:
            selected.append(parm_tuple)
            continue
        if template.get("class") != "RampParmTemplate":
            leading_defaults.append(parm_tuple)

    # Preserve the top of the actual Parameter Pane even on an untouched node,
    # matching compact mode's useful-default floor. Changed menu selectors are
    # retained above; untouched selectors are defaults and need no repetition.
    if len(selected) < minimum_rows:
        for parm_tuple in leading_defaults:
            if parm_tuple not in selected:
                selected.append(parm_tuple)
            if len(selected) >= minimum_rows:
                break

    # Houdini can place multiple ParmTemplates on one visual row. If one side
    # of such a row is selected, retain its partner so a hidden-label checkbox
    # never leaks its internal name into the text.
    selected_ids = {id(parm_tuple) for parm_tuple in selected}
    for index, parm_tuple in enumerate(parameters):
        template = parm_tuple.get("template", {}) or {}
        if id(parm_tuple) in selected_ids and template.get("join_with_next") is True:
            if index + 1 < len(parameters) and _smart_is_value_parameter(parameters[index + 1]):
                selected.append(parameters[index + 1])
                selected_ids.add(id(parameters[index + 1]))
        if id(parm_tuple) in selected_ids and template.get("is_label_hidden") is True and index > 0:
            previous = parameters[index - 1]
            previous_template = previous.get("template", {}) or {}
            if previous_template.get("join_with_next") is True and _smart_is_value_parameter(previous):
                selected.append(previous)
                selected_ids.add(id(previous))

    parameter_order = {id(parm_tuple): index for index, parm_tuple in enumerate(parameters)}
    return sorted(
        {id(parm_tuple): parm_tuple for parm_tuple in selected}.values(),
        key=lambda parm_tuple: parameter_order.get(id(parm_tuple), 0),
    )


def _smart_evaluated_value(parm_tuple: Dict[str, Any]) -> Any:
    value = parm_tuple.get("values")
    if value is None:
        values = [
            parm.get("evaluated_value")
            for parm in parm_tuple.get("parms", []) or []
            if parm.get("evaluated_value") is not None
        ]
        value = values if values else parm_tuple.get("raw_values")
    if isinstance(value, (list, tuple)) and len(value) == 1:
        return value[0]
    return value


def _smart_toggle_label(value: Any) -> str:
    if isinstance(value, str):
        normalized = value.strip().lower()
        if normalized in ("0", "off", "false", "no"):
            return "Off"
        if normalized in ("1", "on", "true", "yes"):
            return "On"
    return "On" if bool(value) else "Off"


def _smart_plain_value(value: Any) -> str:
    value = _compact_prepare_value(value)
    if isinstance(value, (list, tuple)):
        return "(" + ", ".join(_smart_plain_value(component) for component in value) + ")"
    if isinstance(value, dict):
        return json.dumps(value, ensure_ascii=False, sort_keys=True)
    if isinstance(value, float):
        return "%g" % value
    if value is None:
        return "none"
    return str(value).replace("\n", "\\n")


def _smart_value_text(parm_tuple: Dict[str, Any], ramp_summary: Optional[str] = None) -> str:
    if ramp_summary:
        return _markdown_inline_code(ramp_summary, 240)
    value = _smart_evaluated_value(parm_tuple)
    template = parm_tuple.get("template", {}) or {}
    if _smart_is_menu(parm_tuple):
        menu_value = value
        items, _labels = _smart_menu_data(parm_tuple)
        for parm in parm_tuple.get("parms", []) or []:
            for key in ("unexpanded_string", "raw_value"):
                candidate = parm.get(key)
                if candidate is not None and any(str(item) == str(candidate) for item in items):
                    menu_value = candidate
                    break
        label = _compact_menu_value_label(parm_tuple, menu_value)
        if label is None:
            # Never fall back to opaque numeric menu indices in this mode.
            return "*UI choice label unavailable*"
        return _markdown_inline_code(label)
    if template.get("class") == "ToggleParmTemplate":
        return _markdown_inline_code(_smart_toggle_label(value))
    return _markdown_inline_code(_smart_plain_value(value), 240)


def _smart_component_label(index: int, count: int, component_labels: Sequence[Any]) -> Optional[str]:
    if count <= 1:
        return None
    if index < len(component_labels):
        label = str(component_labels[index] or "").strip()
        if label and not label.isdigit():
            return "%s component" % label
    ordinals = ("first", "second", "third", "fourth")
    if index < len(ordinals):
        return "%s component" % ordinals[index]
    return "component %d" % (index + 1)


def _smart_component_expression_sources(parm_tuple: Dict[str, Any]) -> List[Optional[str]]:
    parms = parm_tuple.get("parms", []) or []
    if parm_tuple.get("is_at_default") is True:
        return [None for _parm in parms]
    template = parm_tuple.get("template", {}) or {}
    default_expressions = template.get("default_expression")
    if not isinstance(default_expressions, (list, tuple)):
        default_expressions = [default_expressions]
    sources: List[Optional[str]] = []
    for index, parm in enumerate(parms):
        source = _parm_record_expression_source(parm)
        if source in (None, ""):
            sources.append(None)
            continue
        default_source = default_expressions[index] if index < len(default_expressions) else None
        if str(source) == str(default_source or ""):
            # Stock HDAs contain many implementation links. They are part of
            # the node definition, not expressions entered by the user.
            sources.append(None)
            continue
        sources.append(str(source))
    return sources


def _smart_value_with_inline_component_expressions(
    parm_tuple: Dict[str, Any],
    ramp_summary: Optional[str] = None,
) -> Tuple[str, bool]:
    normal_value = _smart_value_text(parm_tuple, ramp_summary)
    if ramp_summary or _smart_is_menu(parm_tuple):
        return normal_value, False
    values = _smart_evaluated_value(parm_tuple)
    parms = parm_tuple.get("parms", []) or []
    if not isinstance(values, (list, tuple)) or len(values) <= 1 or len(values) != len(parms):
        return normal_value, False
    sources = _smart_component_expression_sources(parm_tuple)
    if not any(source not in (None, "") for source in sources):
        return normal_value, False
    components = []
    for value, source in zip(values, sources):
        component = _markdown_inline_code(_smart_plain_value(value), 120)
        if source not in (None, ""):
            component += " ← expression " + _markdown_inline_code(source)
        components.append(component)
    return "(" + ", ".join(components) + ")", True


def _smart_expression_sources(parm_tuple: Dict[str, Any]) -> List[str]:
    parms = parm_tuple.get("parms", []) or []
    template = parm_tuple.get("template", {}) or {}
    component_labels = list(template.get("component_labels") or [])
    sources: List[str] = []
    for index, source in enumerate(_smart_component_expression_sources(parm_tuple)):
        if source in (None, ""):
            continue
        component = _smart_component_label(index, len(parms), component_labels)
        if component:
            sources.append("%s → %s" % (component, _markdown_inline_code(source)))
        else:
            sources.append(_markdown_inline_code(source))
    return sources


def _smart_channel_lines(
    parm_tuple: Dict[str, Any],
    label: str,
    path_base: Optional[str],
) -> List[str]:
    lines: List[str] = []
    parms = parm_tuple.get("parms", []) or []
    template = parm_tuple.get("template", {}) or {}
    component_labels = list(template.get("component_labels") or [])
    default_expressions = template.get("default_expression")
    if not isinstance(default_expressions, (list, tuple)):
        default_expressions = [default_expressions]
    tuple_is_default = parm_tuple.get("is_at_default") is True
    for index, parm in enumerate(parms):
        component = _smart_component_label(index, len(parms), component_labels)
        display_label = "%s %s" % (label, component) if component else label
        source = _parm_record_expression_source(parm)
        default_source = default_expressions[index] if index < len(default_expressions) else None
        is_default_expression = tuple_is_default or (
            source not in (None, "") and str(source) == str(default_source or "")
        )
        referenced_parm = parm.get("referenced_parm")
        if referenced_parm and not is_default_expression:
            target = _compact_path_relative_to_base(referenced_parm, path_base)
            lines.append("  - %s source target: %s" % (display_label, _markdown_inline_code(target)))
        alias = parm.get("alias")
        if alias not in (None, ""):
            lines.append("  - %s channel alias: %s" % (display_label, _markdown_inline_code(alias)))
        chop_override = parm.get("chop_override")
        if isinstance(chop_override, dict) and chop_override:
            lines.append(
                "  - %s CHOP override: %s / %s"
                % (
                    display_label,
                    _markdown_inline_code(chop_override.get("chop_node") or "?"),
                    _markdown_inline_code(chop_override.get("track_name") or "?"),
                )
            )

        keyframes = [] if is_default_expression else list(parm.get("keyframes", []) or [])
        if len(keyframes) == 1:
            only_key = keyframes[0]
            try:
                is_frame_one = float(only_key.get("frame")) == 1.0
            except Exception:
                is_frame_one = False
            only_expression = only_key.get("expression")
            if is_frame_one and (
                only_expression == source or _is_trivial_expression_source(only_expression)
            ):
                keyframes = []
        for keyframe in keyframes:
            frame = keyframe.get("frame")
            time = keyframe.get("time")
            if frame is not None:
                try:
                    position = "F%g" % float(frame)
                except Exception:
                    position = "F%s" % frame
            elif time is not None:
                position = "t=%s" % time
            else:
                position = "position=?"
            fields = []
            if keyframe.get("expression") not in (None, ""):
                fields.append("expression=%s" % _markdown_inline_code(keyframe.get("expression")))
            if keyframe.get("value") is not None:
                fields.append("value=%s" % _markdown_inline_code(keyframe.get("value")))
            if not fields:
                fields.append("key data captured in JSON")
            lines.append("  - %s key %s: %s" % (display_label, position, ", ".join(fields)))
    return lines


def _smart_parameter_lines(
    node: Dict[str, Any],
    parameters: Sequence[Dict[str, Any]],
    path_base: Optional[str],
) -> Tuple[List[str], set]:
    if _smart_is_rbd_node(node):
        minimum_rows = 12
    elif _compact_node_importance(node) >= COMPACT_IMPORTANT_SCORE:
        minimum_rows = DEFAULT_COMPACT_IMPORTANT_PARAM_FLOOR
    else:
        minimum_rows = 0
    selected = _smart_selected_parameters(parameters, minimum_rows=minimum_rows)
    if not selected:
        return [], set()

    lines: List[str] = []
    selected_names = set()
    _ramp_instance_names, ramp_summaries, _changed_ramps = _smart_ramp_state(parameters)
    current_folders: Optional[Tuple[str, ...]] = None
    parameter_order = {id(parm_tuple): index for index, parm_tuple in enumerate(parameters)}
    selected_index = 0
    while selected_index < len(selected):
        parm_tuple = selected[selected_index]
        members = [parm_tuple]
        while members[-1].get("template", {}).get("join_with_next") is True:
            next_selected_index = selected_index + len(members)
            if next_selected_index >= len(selected):
                break
            next_parm = selected[next_selected_index]
            if parameter_order.get(id(next_parm)) != parameter_order.get(id(members[-1]), -2) + 1:
                break
            if tuple(next_parm.get("folders") or []) != tuple(parm_tuple.get("folders") or []):
                break
            members.append(next_parm)

        folders = tuple(str(folder) for folder in (parm_tuple.get("folders") or []) if str(folder))
        if folders != current_folders:
            lines.append("")
            lines.append("#### UI: %s" % (" / ".join(folders) if folders else "Main"))
            lines.append("")
            current_folders = folders

        label_member = next(
            (
                member
                for member in members
                if member.get("template", {}).get("is_label_hidden") is not True
            ),
            members[-1],
        )
        label_template = label_member.get("template", {}) or {}
        label = str(label_member.get("label") or label_template.get("label") or "UI parameter")
        value_texts = []
        inline_expression_members: set = set()
        for member in members:
            member_value, expression_inlined = _smart_value_with_inline_component_expressions(
                member,
                ramp_summaries.get(str(member.get("name") or "")),
            )
            value_texts.append(member_value)
            if expression_inlined:
                inline_expression_members.add(id(member))
        if len(members) > 1:
            labelled_values = []
            for member, member_value in zip(members, value_texts):
                member_template = member.get("template", {}) or {}
                if member_template.get("is_label_hidden") is True:
                    if member_template.get("class") == "ToggleParmTemplate":
                        member_label = "checkbox"
                    elif _smart_is_menu(member):
                        member_label = "choice"
                    else:
                        member_label = "value"
                else:
                    member_label = str(member.get("label") or member_template.get("label") or "UI parameter")
                labelled_values.append("%s: %s" % (member_label, member_value))
            row = "- " + "; ".join(labelled_values)
        else:
            row = "- %s: %s" % (label, value_texts[0])
        expression_sources = []
        for member in members:
            if id(member) not in inline_expression_members:
                expression_sources.extend(_smart_expression_sources(member))
        if expression_sources:
            row += "; expression: " + ", ".join(expression_sources)
        if all(member.get("ui_disabled") is True for member in members):
            row += " *(disabled in the current UI)*"
        lines.append(row)
        for member in members:
            lines.extend(_smart_channel_lines(member, label, path_base))
            if member.get("name"):
                selected_names.add(str(member.get("name")))
        selected_index += len(members)
    return lines, selected_names


def render_compact_markdown(data: Dict[str, Any], smart: bool = False) -> str:
    nodes = sorted(data.get("nodes", []), key=lambda row: str(row.get("path", "")))
    connections = data.get("connections", [])
    code_blocks = data.get("code_blocks", [])
    node_info = _compact_node_info(nodes)

    lines: List[str] = []
    lines.append("# Houdini Scene Summary%s" % _houdini_version_suffix(data))
    lines.append("")
    lines.append("- Exporter: `%s %s`" % (EXPORTER_NAME, SCHEMA_VERSION))
    lines.append("- Connection notation: `A -> B -> C` means each node's first output feeds the next node's first input; other ports are marked like `[output2]` / `[input3: Constraint Geometry]`.")
    if smart:
        lines.append("- Mode: `Smart (experimental)`. Node settings use the current visible Houdini UI labels, folder labels, and menu choice labels; hidden internal parameters and numeric menu tokens are omitted. Code-focused nodes retain their compact code-oriented presentation.")
    lines.append("")

    lines.append("## Connections")
    lines.append("")
    connection_lines = _compact_connection_lines(connections, node_info, nodes)
    if connection_lines:
        lines.extend(connection_lines)
    else:
        lines.append("(none)")
    lines.append("")

    lines.append("## Inspector Settings")
    lines.append("")
    inspector_path_base = _compact_inspector_path_base(nodes)
    if inspector_path_base:
        lines.append(
            "- Path base: `%s/` (node headings below are relative to this exact path)."
            % inspector_path_base.rstrip("/")
        )
        lines.append("")
    inline_code_keys = set()
    for node in _attention_ordered_nodes(nodes):
        node_parameters = node.get("parameters", []) or []
        if (
            _node_type_record_suppresses_parameters(node.get("type", {}))
            and not _parameters_have_channel_details(node_parameters)
        ):
            continue
        code_refs = [block for block in node.get("code_blocks", []) if block.get("node_path") == node.get("path")]
        comment = node.get("comment")
        node_type = node.get("type", {}).get("name_with_category") or node.get("type", {}).get("name")
        type_description = node.get("type", {}).get("description")
        is_wrangle = _compact_is_wrangle_node(node)
        is_smart_node = smart and not is_wrangle
        param_chunks = [] if (is_wrangle or is_smart_node) else _compact_parameter_chunks(node_parameters)
        heading_path = _compact_path_relative_to_base(node.get("path"), inspector_path_base)
        heading = "### `%s` type=`%s`" % (heading_path, node_type)
        if type_description and _compact_condense(type_description) != _compact_condense(_node_type_token(node_type)):
            heading += " (%s)" % type_description
        lines.append(heading)
        flags = _compact_true_flags(node.get("flags", {}))
        if flags:
            lines.append("- Flags: `%s`" % ",".join(flags))
        if comment:
            lines.append("- Comment: %s" % _inline_text(str(comment), 240))
        lines.extend(_render_packed_rig_tree(node.get("packed_rig_tree")))
        if is_wrangle:
            wrangle_lines, wrangle_code_keys = _compact_wrangle_lines(node)
            lines.extend(wrangle_lines)
            inline_code_keys.update(wrangle_code_keys)
        smart_selected_names: set = set()
        if is_smart_node:
            smart_lines, smart_selected_names = _smart_parameter_lines(node, node_parameters, inspector_path_base)
            lines.extend(smart_lines)
            for block in code_refs:
                block_tuple_name = block.get("tuple_name") or block.get("parm_name")
                if str(block_tuple_name or "") not in smart_selected_names:
                    inline_code_keys.add(_compact_code_key(block))
        if param_chunks:
            for chunk in param_chunks:
                lines.append("- Params: %s" % chunk)
        if not is_wrangle and not is_smart_node and _compact_node_importance(node) >= COMPACT_IMPORTANT_SCORE:
            # Count only the entries actually rendered, not hidden folder/ramp noise;
            # otherwise nodes full of "changed" folder parms never get their Defaults floor.
            changed_count = len(_compact_parameter_entries(node.get("parameters", []) or []))
            default_chunks = _compact_default_parameter_chunks(
                node.get("parameters", []) or [],
                DEFAULT_COMPACT_IMPORTANT_PARAM_FLOOR - changed_count,
            )
            for chunk in default_chunks:
                lines.append("- Defaults: %s" % chunk)
        # Expressions are already shown in Params. Compact mode adds only the
        # information Params cannot carry: resolved links, real animation keys,
        # aliases, and CHOP overrides.
        if not is_smart_node:
            lines.extend(
                _render_parameter_channel_details(
                    node_parameters,
                    "- ",
                    include_source=False,
                    compact=True,
                    path_base=inspector_path_base,
                )
            )
        visible_code_refs = [block for block in code_refs if _compact_code_key(block) not in inline_code_keys]
        if visible_code_refs:
            refs = ", ".join(
                "`%s`" % (block.get("parm_name") or str(block.get("parm_path") or "").rsplit("/", 1)[-1])
                for block in visible_code_refs
            )
            lines.append("- Code params: %s" % refs)
        lines.append("")

    if code_blocks:
        visible_code_blocks = [block for block in code_blocks if _compact_code_key(block) not in inline_code_keys]
    else:
        visible_code_blocks = []
    if visible_code_blocks:
        lines.append("## Code")
        lines.append("")
        for index, block in enumerate(visible_code_blocks, 1):
            text_record = block.get("text", {})
            text = text_record.get("text", "") if isinstance(text_record, dict) else ""
            language = block.get("language_guess") or "text"
            code_node = _compact_path_relative_to_base(block.get("node_path"), inspector_path_base)
            code_parm = block.get("parm_name") or str(block.get("parm_path") or "").rsplit("/", 1)[-1]
            lines.append("### Code %d: `%s` parm=`%s`" % (index, code_node, code_parm))
            lines.append("")
            lines.append("```%s" % language)
            lines.append(str(text).rstrip())
            lines.append("```")
            lines.append("")

    errors = data.get("errors", [])
    if errors:
        lines.append("## Export Notes")
        lines.append("")
        for error in errors[:100]:
            lines.append("- `%s`: %s: %s" % (error.get("context"), error.get("error_type"), error.get("message")))
        if len(errors) > 100:
            lines.append("- ... %d more errors omitted" % (len(errors) - 100))
        lines.append("")

    lines.extend(_llm_footer_lines(data))
    return "\n".join(lines).rstrip() + "\n"


def _compact_node_info(nodes: Sequence[Dict[str, Any]]) -> Dict[str, Dict[str, Any]]:
    info: Dict[str, Dict[str, Any]] = {}
    for node in nodes:
        path = node.get("path")
        if not path:
            continue
        node_type = node.get("type", {}) or {}
        info[str(path)] = {
            "name": node.get("name") or str(path).rsplit("/", 1)[-1],
            "type_name": node_type.get("name"),
            "type_label": node_type.get("description") or node_type.get("name"),
        }
    return info


def _compact_condense(text: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "", str(text or "").lower())


def _compact_name_matches_type(name: Any, info: Dict[str, Any]) -> bool:
    base = re.sub(r"[\d_]+$", "", str(name or "").lower())
    condensed_name = _compact_condense(base)
    if not condensed_name:
        return False
    candidates = {
        _compact_condense(_node_type_token(info.get("type_name"))),
        _compact_condense(info.get("type_label")),
    }
    candidates.discard("")
    return any(condensed_name.startswith(candidate) for candidate in candidates)


def _compact_node_ref(path: Optional[str], parent: str, node_info: Dict[str, Dict[str, Any]]) -> str:
    if not path:
        return "`?`"
    display = str(path)
    parent_prefix = parent.rstrip("/") + "/"
    if display.startswith(parent_prefix):
        display = display[len(parent_prefix):]
    info = node_info.get(str(path))
    if info is None or _compact_name_matches_type(info.get("name"), info):
        return "`%s`" % display
    return "`%s` (%s)" % (display, info.get("type_label") or "?")


def _compact_port_is_primary(value: Any) -> bool:
    if value is None:
        return True
    try:
        return int(value) == 0
    except Exception:
        return False


def _compact_port_text(direction: str, endpoint: Dict[str, Any]) -> str:
    name = endpoint.get("%s_name" % direction)
    label = endpoint.get("%s_label" % direction)
    index = endpoint.get("%s_index" % direction)
    token = str(name).strip() if name not in (None, "") else ""
    if not token:
        token = "%s %s" % (direction, index)
    elif direction not in token.lower():
        token = "%s %s" % (direction, token)
    label_text = str(label).strip() if label not in (None, "") else ""
    if (
        label_text
        and not label_text.lower().startswith(direction)
        and _compact_condense(label_text) != _compact_condense(token)
    ):
        if len(label_text) > 60:
            label_text = label_text[:57].rstrip() + "..."
        token = "%s: %s" % (token, label_text)
    return "[%s]" % token


def _compact_connection_lines(
    connections: Sequence[Dict[str, Any]],
    node_info: Dict[str, Dict[str, Any]],
    nodes: Optional[Sequence[Dict[str, Any]]] = None,
) -> List[str]:
    groups: Dict[str, List[Dict[str, Any]]] = {}
    connected_paths: set = set()
    for connection in connections:
        anchor = _connection_endpoint_path(connection, "target") or _connection_endpoint_path(connection, "source")
        if not anchor:
            continue
        parent = str(anchor).rsplit("/", 1)[0] or "/"
        groups.setdefault(parent, []).append(connection)
        for endpoint_name in ("source", "target"):
            path = _connection_endpoint_path(connection, endpoint_name)
            if path:
                connected_paths.add(path)

    nodes_by_parent: Dict[str, List[str]] = {}
    for node in nodes or ():
        path = node.get("path")
        if not path:
            continue
        parent = str(path).rsplit("/", 1)[0] or "/"
        nodes_by_parent.setdefault(parent, []).append(str(path))

    lines: List[str] = []
    show_headings = len(groups) > 1
    for parent in sorted(groups):
        if show_headings:
            if lines:
                lines.append("")
            lines.append("### `%s`" % parent)
        chain_edges: List[Tuple[str, str]] = []
        port_connections: List[Dict[str, Any]] = []
        for connection in groups[parent]:
            source = connection.get("source", {}) or {}
            target = connection.get("target", {}) or {}
            source_path = _connection_endpoint_path(connection, "source")
            target_path = _connection_endpoint_path(connection, "target")
            if not source_path or not target_path:
                continue
            if _compact_port_is_primary(source.get("output_index")) and _compact_port_is_primary(target.get("input_index")):
                chain_edges.append((source_path, target_path))
            else:
                port_connections.append(connection)

        chain_lines = []
        for chain in _compact_chains(chain_edges):
            chain_lines.append("- " + " -> ".join(_compact_node_ref(path, parent, node_info) for path in chain))
        lines.extend(sorted(chain_lines))

        port_lines = []
        for connection in port_connections:
            source = connection.get("source", {}) or {}
            target = connection.get("target", {}) or {}
            pieces = [_compact_node_ref(_connection_endpoint_path(connection, "source"), parent, node_info)]
            if not _compact_port_is_primary(source.get("output_index")):
                pieces.append(_compact_port_text("output", source))
            pieces.append("->")
            pieces.append(_compact_node_ref(_connection_endpoint_path(connection, "target"), parent, node_info))
            if not _compact_port_is_primary(target.get("input_index")):
                pieces.append(_compact_port_text("input", target))
            port_lines.append("- " + " ".join(pieces))
        lines.extend(sorted(port_lines))

        unwired = sorted(path for path in nodes_by_parent.get(parent, []) if path not in connected_paths)
        if unwired:
            refs = ", ".join(_compact_node_ref(path, parent, node_info) for path in unwired)
            lines.append("- Not wired: %s" % refs)
    return lines


def _compact_chains(edges: Sequence[Tuple[str, str]]) -> List[List[str]]:
    unique_edges = sorted(set(edges))
    out_edges: Dict[str, List[str]] = {}
    in_count: Dict[str, int] = {}
    for source, target in unique_edges:
        out_edges.setdefault(source, []).append(target)
        in_count[target] = in_count.get(target, 0) + 1

    def is_pass_through(path: str) -> bool:
        return len(out_edges.get(path, [])) == 1 and in_count.get(path, 0) == 1

    chains: List[List[str]] = []
    covered: set = set()
    for source, target in unique_edges:
        if is_pass_through(source):
            continue  # This edge is emitted as part of the chain that flows through `source`.
        chain = [source, target]
        covered.add((source, target))
        seen = {source, target}
        current = target
        while is_pass_through(current):
            next_path = out_edges[current][0]
            if next_path in seen:
                break
            covered.add((current, next_path))
            chain.append(next_path)
            seen.add(next_path)
            current = next_path
        chains.append(chain)

    for source, target in unique_edges:
        if (source, target) not in covered:
            chains.append([source, target])
    return chains


def _compact_true_flags(flags: Dict[str, Any]) -> List[str]:
    interesting = []
    # isLockedHDA is omitted: every stock HDA instance reports it, so it carries no signal.
    for key in ("isDisplayFlagSet", "isRenderFlagSet", "isTemplateFlagSet", "isBypassed", "isHardLocked", "isSoftLocked"):
        if flags.get(key) is True:
            name = key[2:] if key.startswith("is") else key
            if name.endswith("FlagSet"):
                name = name[: -len("FlagSet")]
            interesting.append(name)
    return interesting


def _compact_is_wrangle_node(node: Dict[str, Any]) -> bool:
    node_type = node.get("type", {})
    text = " ".join(str(node_type.get(key) or "") for key in ("name", "name_with_category", "description")).lower()
    return "wrangle" in text


# Built-in wrangle parms already covered by the Run over / Group / VEX lines or
# that only tune VEX compilation; anything else on a wrangle is a user-made spare
# parm referenced by ch()/chv()/chf() in the snippet, so its value matters.
_WRANGLE_BUILTIN_PARM_NAMES = {
    "group", "grouptype", "class", "snippet", "exportlist", "autobind",
    "groupbindings", "bindings", "nattribs", "vexpression",
}


def _compact_wrangle_lines(node: Dict[str, Any]) -> Tuple[List[str], set]:
    parameters = node.get("parameters", [])
    lines = []
    inline_code_keys = set()

    run_over = _compact_wrangle_run_over(parameters)
    if run_over:
        lines.append("- Run over: `%s`" % run_over)

    group_value = _compact_parameter_scalar(_compact_parameter_by_name(parameters, "group"))
    if isinstance(group_value, str) and group_value:
        lines.append("- Group: `%s`" % _inline_text(group_value, 160))

    spare_parameters = [
        parm_tuple
        for parm_tuple in parameters
        if str(parm_tuple.get("name") or "") not in _WRANGLE_BUILTIN_PARM_NAMES
        and not str(parm_tuple.get("name") or "").startswith(("vex_", "bind"))
    ]
    for chunk in _compact_parameter_chunks(spare_parameters, include_labels=True):
        lines.append("- Params: %s" % chunk)

    snippet = _compact_parameter_scalar(_compact_parameter_by_name(parameters, "snippet"))
    if isinstance(snippet, str) and snippet:
        lines.append("- VEX:")
        lines.append("")
        lines.append("```c")
        lines.append(snippet.rstrip())
        lines.append("```")
        for block in node.get("code_blocks", []):
            if (block.get("tuple_name") == "snippet" or block.get("parm_name") == "snippet" or str(block.get("parm_path") or "").endswith("/snippet")):
                inline_code_keys.add(_compact_code_key(block))
    return lines, inline_code_keys


def _compact_wrangle_run_over(parameters: Sequence[Dict[str, Any]]) -> Optional[str]:
    parm_tuple = _compact_parameter_by_name(parameters, "class")
    value = _compact_parameter_scalar(parm_tuple)
    if value is None:
        return None
    label = _compact_menu_value_label(parm_tuple, value)
    if label:
        return label
    try:
        index = int(value)
    except Exception:
        index = None
    if index in WRANGLE_RUN_OVER_BY_INDEX:
        return WRANGLE_RUN_OVER_BY_INDEX[index]
    return _compact_plain_text(value, 80)


def _compact_parameter_by_name(parameters: Sequence[Dict[str, Any]], name: str) -> Optional[Dict[str, Any]]:
    for parm_tuple in parameters:
        if parm_tuple.get("name") == name:
            return parm_tuple
    return None


def _parameter_tuple_expression_value(parm_tuple: Dict[str, Any]) -> Tuple[bool, Any]:
    """Return a component-aligned raw value when any component has an expression."""
    parms = parm_tuple.get("parms", []) or []
    if not any(_parm_record_expression_source(parm) is not None for parm in parms):
        return False, None

    values: List[Any] = []
    for parm in parms:
        expression_source = _parm_record_expression_source(parm)
        if expression_source is not None:
            values.append(expression_source)
            continue
        value = None
        for key in ("unexpanded_string", "raw_value"):
            candidate = parm.get(key)
            if candidate is not None:
                evaluated = parm.get("evaluated_value")
                value = evaluated if _is_trivial_expression_source(candidate) and evaluated is not None else candidate
                break
        if value is None:
            value = parm.get("evaluated_value")
        values.append(value)

    if len(values) == 1:
        return True, values[0]
    return True, values


def _compact_parameter_scalar(parm_tuple: Optional[Dict[str, Any]]) -> Any:
    if not parm_tuple:
        return None
    has_expression, expression_value = _parameter_tuple_expression_value(parm_tuple)
    if has_expression:
        return expression_value
    value = parm_tuple.get("values")
    if value is None:
        values = []
        for parm in parm_tuple.get("parms", []):
            for key in ("evaluated_value", "expression", "unexpanded_string", "raw_value"):
                candidate = parm.get(key)
                if candidate is not None:
                    values.append(candidate)
                    break
        if not values:
            return None
        value = values
    if isinstance(value, (list, tuple)) and len(value) == 1:
        return value[0]
    return value


def _compact_menu_value_label(parm_tuple: Optional[Dict[str, Any]], value: Any) -> Optional[str]:
    if not parm_tuple:
        return None
    template = parm_tuple.get("template", {}) or {}
    labels = template.get("menu_labels") or []
    items = template.get("menu_items") or []
    # parm.menuItems()/menuLabels() reflect script-generated menus at the
    # current node state.  Prefer them over the static ParmTemplate snapshot.
    # This is especially important for RBD HDAs whose choices change with the
    # selected material/mode.
    for parm in parm_tuple.get("parms", []) or []:
        live_labels = parm.get("menu_labels") or []
        live_items = parm.get("menu_items") or []
        if live_labels or live_items:
            labels = live_labels
            items = live_items
            break
    if items and labels:
        value_text = str(value)
        for item, label in zip(items, labels):
            if str(item) == value_text:
                return str(label)
    try:
        index = int(value)
    except Exception:
        index = None
    if index is not None and 0 <= index < len(labels):
        return str(labels[index])
    if index is not None and 0 <= index < len(items):
        return str(items[index])
    return None


def _compact_code_key(block: Dict[str, Any]) -> Tuple[Any, Any, Any]:
    return (block.get("node_path"), block.get("parm_path"), block.get("tuple_name") or block.get("parm_name"))


_RAMP_INSTANCE_PATTERN = re.compile(r"^(?P<base>.+?)(?P<index>\d+)(?P<channel>pos|value|interp|c)$")


def _compact_folder_is_noise(template: Dict[str, Any]) -> bool:
    """Folder open/close state parms carry no scene meaning; multiparm counts do."""
    if template.get("class") not in ("FolderParmTemplate", "FolderSetParmTemplate"):
        return False
    folder_type = str(template.get("folder_type") or "")
    return "Multiparm" not in folder_type and "RadioButtons" not in folder_type


def _compact_ramp_number(value: Any) -> str:
    if isinstance(value, (list, tuple)):
        return "(" + ",".join(_compact_ramp_number(v) for v in value) + ")"
    if isinstance(value, float):
        return "%g" % value
    if value is None:
        return "?"
    return str(value)


def _compact_ramp_summary(instances: Dict[int, Dict[str, Any]]) -> Optional[str]:
    if not instances:
        return None
    interps = {str(inst.get("interp")) for inst in instances.values() if inst.get("interp") is not None}
    uniform_interp = interps.pop() if len(interps) == 1 else None
    pieces = []
    for index in sorted(instances):
        inst = instances[index]
        pos = _compact_ramp_number(inst.get("pos"))
        value = _compact_ramp_number(inst.get("value") if "value" in inst else inst.get("c"))
        if uniform_interp is not None or inst.get("interp") is None:
            pieces.append("(%s, %s)" % (pos, value))
        else:
            pieces.append("(%s, %s, %s)" % (pos, value, inst.get("interp")))
    text = "ramp " + " ".join(pieces)
    if uniform_interp:
        text += " @ %s" % uniform_interp
    return text


def _compact_parameter_chunks(
    parameters: Sequence[Dict[str, Any]],
    max_per_line: int = 6,
    max_params: int = DEFAULT_COMPACT_PARAMETER_LIMIT,
    include_labels: bool = False,
) -> List[str]:
    entries = _compact_parameter_entries(parameters, include_labels)
    if max_params >= 0 and len(entries) > max_params:
        omitted = len(entries) - max_params
        entries = entries[:max_params]
        entries.append("... +%d more omitted (unknown here; not assumed default)" % omitted)
    chunks = []
    for index in range(0, len(entries), max_per_line):
        chunks.append("; ".join(entries[index : index + max_per_line]))
    return chunks


def _compact_parameter_entries(
    parameters: Sequence[Dict[str, Any]],
    include_labels: bool = False,
) -> List[str]:
    ramp_names = {
        str(parm_tuple.get("name"))
        for parm_tuple in parameters
        if (parm_tuple.get("template", {}) or {}).get("class") == "RampParmTemplate"
    }
    ramp_instances: Dict[str, Dict[int, Dict[str, Any]]] = {}
    ramp_changed: set = set()
    for parm_tuple in parameters:
        name = str(parm_tuple.get("name") or "")
        if name in ramp_names:
            if parm_tuple.get("is_at_default") is False or _parameter_tuple_expression_value(parm_tuple)[0]:
                ramp_changed.add(name)
            continue
        if not ramp_names:
            continue
        match = _RAMP_INSTANCE_PATTERN.match(name)
        if not match or match.group("base") not in ramp_names:
            continue
        base = match.group("base")
        channel = match.group("channel")
        slot = ramp_instances.setdefault(base, {}).setdefault(int(match.group("index")), {})
        if channel == "interp":
            label = _compact_menu_value_label(parm_tuple, _compact_parameter_scalar(parm_tuple))
            slot[channel] = label if label is not None else _compact_parameter_scalar(parm_tuple)
        else:
            slot[channel] = _compact_parameter_scalar(parm_tuple)
        if parm_tuple.get("is_at_default") is False or _parameter_tuple_expression_value(parm_tuple)[0]:
            ramp_changed.add(base)

    entries = []
    emitted_ramps: set = set()
    for parm_tuple in parameters:
        name = str(parm_tuple.get("name") or "")
        template = parm_tuple.get("template", {}) or {}
        if template.get("class") in _ULTRA_UI_NOISE_TEMPLATE_CLASSES:
            continue
        if _compact_folder_is_noise(template):
            continue
        if name in ramp_names:
            if name in ramp_changed and name not in emitted_ramps:
                summary = _compact_ramp_summary(ramp_instances.get(name, {}))
                if summary:
                    entries.append("`%s`=`%s`" % (name, summary))
            emitted_ramps.add(name)
            continue
        if ramp_names:
            match = _RAMP_INSTANCE_PATTERN.match(name)
            if match and match.group("base") in ramp_names:
                continue
        if parm_tuple.get("is_at_default") is True and not _parameter_tuple_expression_value(parm_tuple)[0]:
            continue
        entry = _compact_parameter_entry(parm_tuple, include_labels)
        if entry:
            entries.append(entry)
    return entries


def _compact_parameter_entry(parm_tuple: Dict[str, Any], include_label: bool = False) -> Optional[str]:
    name = parm_tuple.get("name")
    if not name:
        return None
    value = _compact_parameter_value(parm_tuple)
    if value is None:
        return None
    has_expression, _expression_value = _parameter_tuple_expression_value(parm_tuple)
    operator = " expression=" if has_expression else "="
    if include_label:
        label = parm_tuple.get("label")
        if label and _compact_condense(label) != _compact_condense(str(name)):
            return "`%s` (%s)%s%s" % (name, label, operator, value)
    return "`%s`%s%s" % (name, operator, value)


def _compact_parameter_value(parm_tuple: Dict[str, Any]) -> Optional[str]:
    has_expression, expression_value = _parameter_tuple_expression_value(parm_tuple)
    if has_expression:
        return _compact_value_text(expression_value)
    template = parm_tuple.get("template", {}) or {}
    if template.get("menu_items") or template.get("menu_labels"):
        menu_label = _compact_menu_value_label(parm_tuple, _compact_parameter_scalar(parm_tuple))
        if menu_label is not None:
            return _compact_value_text(menu_label)
    if parm_tuple.get("values_evaluated") and parm_tuple.get("values") is not None:
        return _compact_value_text(parm_tuple.get("values"))
    values = []
    for parm in parm_tuple.get("parms", []):
        value = None
        for key in ("expression", "unexpanded_string", "raw_value", "evaluated_value"):
            candidate = parm.get(key)
            if candidate is not None:
                value = candidate
                break
        if value is not None:
            values.append(value)
    if not values:
        tuple_value = parm_tuple.get("values")
        if tuple_value is not None:
            values = [tuple_value]
    if not values:
        return None
    if len(values) == 1:
        return _compact_value_text(values[0])
    return _compact_value_text(values)


def _compact_value_text(value: Any, limit: int = 160) -> str:
    return _markdown_inline_code(_compact_plain_text(value, limit), limit)


def _compact_opaque_text_summary(text: str) -> Optional[str]:
    if len(text) < 256:
        return None
    no_whitespace = not bool(re.search(r"\s", text))
    is_hex_blob = no_whitespace and bool(re.fullmatch(r"[0-9A-Fa-f]+", text))
    if no_whitespace:
        simple_chars = sum(character.isalnum() or character in "+/=_-" for character in text)
        is_encoded_blob = len(text) >= 1024 and simple_chars / float(len(text)) >= 0.98
    else:
        is_encoded_blob = False
    if not (is_hex_blob or is_encoded_blob):
        return None
    return "<opaque data: %d chars, sha256=%s>" % (len(text), _sha256_text(text)[:16])


def _compact_prepare_value(value: Any) -> Any:
    if isinstance(value, str):
        return _compact_opaque_text_summary(value) or value
    if isinstance(value, (list, tuple)):
        return [_compact_prepare_value(item) for item in value]
    if isinstance(value, dict):
        return {str(key): _compact_prepare_value(item) for key, item in value.items()}
    return value


def _compact_plain_text(value: Any, limit: int = 160) -> str:
    value = _compact_prepare_value(value)
    if isinstance(value, str):
        text = value
    else:
        text = json.dumps(value, ensure_ascii=False)
    text = text.replace("\n", "\\n")
    if len(text) > limit:
        text = text[:limit] + "..."
    return text


DEFAULT_ULTRA_MAX_RUNS = 2000
DEFAULT_ULTRA_SAMPLE_COUNT = 5


def _ultra_value_text(value: Any) -> str:
    if isinstance(value, str):
        return json.dumps(value, ensure_ascii=False)
    return _compact_ramp_number(value)


def _ultra_compress_values(values: Sequence[Any]) -> List[str]:
    """Run-length encode consecutive equal values: 0.5, 0.5, 0.5 -> `0.5 (x3)`."""
    pieces: List[str] = []
    run_text: Optional[str] = None
    run_count = 0
    for value in values:
        text = _ultra_value_text(value)
        if text == run_text:
            run_count += 1
            continue
        if run_text is not None:
            pieces.append(run_text if run_count == 1 else "%s (x%d)" % (run_text, run_count))
        run_text = text
        run_count = 1
    if run_text is not None:
        pieces.append(run_text if run_count == 1 else "%s (x%d)" % (run_text, run_count))
    return pieces


_ULTRA_UI_NOISE_TEMPLATE_CLASSES = ("SeparatorParmTemplate", "LabelParmTemplate", "ButtonParmTemplate")


def _expression_metadata_text(kind: Any, language: Any) -> str:
    pieces = []
    if language not in (None, ""):
        pieces.append(str(language).rsplit(".", 1)[-1])
    if kind not in (None, ""):
        pieces.append(str(kind))
    return ", ".join(pieces)


def _markdown_inline_code(value: Any, limit: int = 500) -> str:
    text = _inline_text(str(value), limit)
    longest_run = max((len(run) for run in re.findall(r"`+", text)), default=0)
    fence = "`" * (longest_run + 1)
    padding = " " if text.startswith("`") or text.endswith("`") else ""
    return "%s%s%s%s%s" % (fence, padding, text, padding, fence)


def _parameter_channel_detail_lines(
    parm: Dict[str, Any],
    indent: str = "- ",
    include_source: bool = True,
    compact: bool = False,
    path_base: Optional[str] = None,
) -> List[str]:
    """Render unevaluated channel, keyframe, reference, and CHOP details."""
    lines: List[str] = []
    name = parm.get("name") or parm.get("path") or "?"
    source = _parm_record_expression_source(parm)
    language = parm.get("expression_language")
    kind = parm.get("expression_kind") or _expression_source_kind(source, language)
    metadata = _expression_metadata_text(kind, language)
    metadata_suffix = " [%s]" % metadata if metadata else ""

    if include_source and source not in (None, ""):
        lines.append(
            "%sChannel source `%s`%s: %s"
            % (indent, name, metadata_suffix, _markdown_inline_code(source))
        )

    alias = parm.get("alias")
    if alias not in (None, ""):
        lines.append("%sChannel alias `%s`: %s" % (indent, name, _markdown_inline_code(alias)))

    referenced_parm = parm.get("referenced_parm")
    if referenced_parm:
        reference_display = _compact_path_relative_to_base(referenced_parm, path_base)
        lines.append(
            "%sChannel reference target `%s`: %s"
            % (indent, name, _markdown_inline_code(reference_display))
        )

    chop_override = parm.get("chop_override")
    if isinstance(chop_override, dict) and chop_override:
        chop_node = chop_override.get("chop_node") or "?"
        track_name = chop_override.get("track_name") or "?"
        suffixes = []
        if chop_override.get("active") is not None:
            suffixes.append("active=%s" % chop_override.get("active"))
        if chop_override.get("num_samples") is not None:
            suffixes.append("samples=%s" % chop_override.get("num_samples"))
        if chop_override.get("override_parm"):
            suffixes.append("override_parm=%s" % _markdown_inline_code(chop_override.get("override_parm")))
        suffix = " (" + ", ".join(suffixes) + ")" if suffixes else ""
        lines.append(
            "%sCHOP override `%s`: %s track=%s%s"
            % (
                indent,
                name,
                _markdown_inline_code(chop_node),
                _markdown_inline_code(track_name),
                suffix,
            )
        )

    keyframes = parm.get("keyframes", []) or []
    visible_keyframes = list(keyframes)
    if compact and len(keyframes) == 1:
        only_key = keyframes[0]
        only_expression = only_key.get("expression")
        try:
            is_frame_one = float(only_key.get("frame")) == 1.0
        except Exception:
            is_frame_one = False
        repeats_source = (
            source not in (None, "")
            and only_expression == source
            and _expression_source_kind(only_expression, only_key.get("expression_language"))
            != "keyframe_interpolation"
        )
        if is_frame_one and (repeats_source or _is_trivial_expression_source(only_expression)):
            # Houdini stores a regular channel expression as one key at F1.
            # Params already contains that source, so the key line adds nothing.
            visible_keyframes = []

    for keyframe in visible_keyframes:
        frame = keyframe.get("frame")
        time = keyframe.get("time")
        if frame is not None:
            try:
                position = "F%g" % float(frame)
            except Exception:
                position = "F%s" % frame
        elif time is not None:
            position = "t=%s" % time
        else:
            position = "position=?"
        key_expression = keyframe.get("expression")
        key_language = keyframe.get("expression_language")
        key_kind = keyframe.get("expression_kind") or _expression_source_kind(key_expression, key_language)
        key_metadata = _expression_metadata_text(key_kind, key_language)
        key_metadata_suffix = " [%s]" % key_metadata if key_metadata else ""
        fields = []
        if key_expression not in (None, ""):
            fields.append("expression=%s" % _markdown_inline_code(key_expression))
        if keyframe.get("value") is not None:
            fields.append("value=%s" % _markdown_inline_code(keyframe.get("value")))
        for field_name in ("slope", "in_slope", "out_slope", "accel"):
            field_value = keyframe.get(field_name)
            if field_value is not None:
                if compact:
                    try:
                        if float(field_value) == 0.0:
                            continue
                    except Exception:
                        pass
                fields.append("%s=%s" % (field_name, _markdown_inline_code(field_value)))
        if not fields:
            fields.append("data captured in JSON")
        lines.append(
            "%sKeyframe `%s` %s%s: %s"
            % (indent, name, position, key_metadata_suffix, ", ".join(fields))
        )
    return lines


def _parameters_have_channel_details(parameters: Sequence[Dict[str, Any]]) -> bool:
    for parm_tuple in parameters:
        for parm in parm_tuple.get("parms", []) or []:
            if (
                _parm_record_expression_source(parm) not in (None, "")
                or _parameter_channel_detail_lines(parm, compact=True)
                or parm.get("referenced_parm")
                or parm.get("chop_override")
                or parm.get("alias")
            ):
                return True
    return False


def _render_parameter_channel_details(
    parameters: Sequence[Dict[str, Any]],
    indent: str = "- ",
    include_source: bool = True,
    compact: bool = False,
    path_base: Optional[str] = None,
) -> List[str]:
    lines: List[str] = []
    for parm_tuple in parameters:
        for parm in parm_tuple.get("parms", []) or []:
            lines.extend(
                _parameter_channel_detail_lines(
                    parm,
                    indent,
                    include_source,
                    compact,
                    path_base,
                )
            )
    return lines


def _ultra_parameter_lines(parameters: Sequence[Dict[str, Any]]) -> List[str]:
    visible: List[Dict[str, Any]] = []
    for parm_tuple in parameters:
        template = parm_tuple.get("template", {}) or {}
        if template.get("class") in _ULTRA_UI_NOISE_TEMPLATE_CLASSES:
            continue
        if _compact_folder_is_noise(template):
            continue
        visible.append(parm_tuple)
    default_count = sum(
        1
        for parm_tuple in visible
        if parm_tuple.get("is_at_default") is True and not _parameter_tuple_expression_value(parm_tuple)[0]
    )

    lines: List[str] = []
    chunks = _compact_parameter_chunks(visible, max_per_line=1, max_params=-1, include_labels=True)
    if chunks:
        lines.append("- Parameters (changed from defaults):")
        for chunk in chunks:
            lines.append("  - %s" % chunk)
    lines.extend(_render_parameter_channel_details(visible, "  - ", include_source=True))
    if default_count:
        lines.append("- %d parameters at default omitted (full values are in the JSON export)" % default_count)
    return lines


def _ultra_attribute_lines(owner: str, attrib: Dict[str, Any], total_elements: Any) -> List[str]:
    name = attrib.get("name")
    type_text = str(attrib.get("data_type") or attrib.get("type") or "?")
    if "." in type_text:
        type_text = type_text.rsplit(".", 1)[-1]
    type_text = type_text.lower()
    size = attrib.get("size")
    try:
        if size is not None and int(size) > 1:
            type_text += "[%s]" % size
    except Exception:
        pass
    if attrib.get("is_array"):
        type_text += " array"
    scope = attrib.get("scope")
    scope_text = "" if scope in (None, "public", "default") else " scope=%s" % scope

    samples = attrib.get("sample_values") or []
    values = [sample.get("value") for sample in samples]
    lines = ["#### %s `%s` (%s)%s" % (owner, name, type_text, scope_text), ""]
    if not values:
        lines.append("(values not captured)")
        lines.append("")
        return lines

    note = ""
    try:
        if total_elements is not None and len(values) < int(total_elements):
            note = "first %d of %s elements" % (len(values), total_elements)
    except Exception:
        pass

    pieces = _ultra_compress_values(values)
    omitted_runs = 0
    if len(pieces) > DEFAULT_ULTRA_MAX_RUNS:
        omitted_runs = len(pieces) - DEFAULT_ULTRA_MAX_RUNS
        pieces = pieces[:DEFAULT_ULTRA_MAX_RUNS]
    if note:
        lines.append("(%s)" % note)
    lines.append("```text")
    for index in range(0, len(pieces), 8):
        lines.append(", ".join(pieces[index : index + 8]))
    if omitted_runs:
        lines.append("... +%d more runs omitted" % omitted_runs)
    lines.append("```")
    lines.append("")
    return lines


_ULTRA_OWNER_PLURALS = {"point": "points", "vertex": "vertices", "primitive": "primitives", "edge": "edges"}


def _ultra_group_lines(owner: str, record: Dict[str, Any], total_elements: Any) -> List[str]:
    plural = _ULTRA_OWNER_PLURALS.get(owner, owner + "s")
    count = record.get("count")
    if count is None:
        size_text = "size unknown"
    elif total_elements not in (None, 0):
        size_text = "%s of %s %s" % (count, total_elements, plural)
    else:
        size_text = "%s %s" % (count, plural)
    suffix = ", ordered" if record.get("is_ordered") else ""
    return ["#### %s group `%s` (%s%s)" % (owner, record.get("name"), size_text, suffix), ""]


def _ultra_geometry_lines(summary: Dict[str, Any]) -> List[str]:
    lines: List[str] = []
    counts = summary.get("counts", {}) or {}
    lines.append(
        "- Geometry: points=`%s`, vertices=`%s`, primitives=`%s`"
        % (counts.get("points"), counts.get("vertices"), counts.get("primitives"))
    )
    lines.append("")

    element_totals = {
        "point": counts.get("points"),
        "vertex": counts.get("vertices"),
        "primitive": counts.get("primitives"),
        "global": 1,
    }
    attributes = summary.get("attributes", {}) or {}
    groups = summary.get("groups", {}) if isinstance(summary.get("groups", {}), dict) else {}
    for owner in ("point", "vertex", "primitive", "global"):
        for record in groups.get(owner, []) or []:
            lines.extend(_ultra_group_lines(owner, record, element_totals.get(owner)))
        for attrib in attributes.get(owner, []) or []:
            lines.extend(_ultra_attribute_lines(owner, attrib, element_totals.get(owner)))
    for record in groups.get("edge", []) or []:
        lines.extend(_ultra_group_lines("edge", record, None))

    omitted = summary.get("omitted_standard_attributes", {}) or {}
    omitted_pieces = []
    if isinstance(omitted, dict):
        for owner in ("point", "vertex", "primitive", "global"):
            for record in omitted.get(owner, []) or []:
                omitted_pieces.append("%s %s" % (owner, record.get("name")))
    if omitted_pieces:
        lines.append("- Standard attributes omitted: `%s`" % "`, `".join(omitted_pieces))
        lines.append("")
    return lines


def render_ultra_markdown(data: Dict[str, Any]) -> str:
    nodes = sorted(data.get("nodes", []), key=lambda row: str(row.get("path", "")))
    node_info = _compact_node_info(nodes)

    lines: List[str] = []
    lines.append("# Houdini Attribute Report%s" % _houdini_version_suffix(data))
    lines.append("")
    lines.append("- Attribute values are listed in element order; `value (xN)` means N consecutive elements share that value.")
    lines.append("")

    connection_lines = _compact_connection_lines(data.get("connections", []), node_info, nodes)
    if connection_lines:
        lines.append("## Connections")
        lines.append("")
        lines.extend(connection_lines)
        lines.append("")

    for node in _attention_ordered_nodes(nodes):
        node_type_record = node.get("type", {}) or {}
        node_type = node_type_record.get("name_with_category") or node_type_record.get("name")
        type_description = node_type_record.get("description")
        heading = "## `%s` type=`%s`" % (node.get("path"), node_type)
        if type_description and _compact_condense(type_description) != _compact_condense(_node_type_token(node_type)):
            heading += " (%s)" % type_description
        lines.append(heading)
        lines.append("")
        flags = _compact_true_flags(node.get("flags", {}) or {})
        if flags:
            lines.append("- Flags: `%s`" % ",".join(flags))
        comment = node.get("comment")
        if comment:
            lines.append("- Comment: %s" % _inline_text(str(comment), 240))
        lines.extend(_render_packed_rig_tree(node.get("packed_rig_tree")))
        lines.extend(_ultra_parameter_lines(node.get("parameters", [])))
        lines.append("")
        geometry_summary = node.get("geometry_summary")
        if geometry_summary:
            lines.append("### Geometry of `%s`" % node.get("path"))
            lines.append("")
            lines.extend(_ultra_geometry_lines(geometry_summary))

    if data.get("code_blocks"):
        lines.extend(_render_code_blocks(data.get("code_blocks", [])))
    if data.get("errors"):
        lines.extend(_render_errors(data.get("errors", [])))
    lines.extend(_llm_footer_lines(data))
    return "\n".join(lines).rstrip() + "\n"


def render_markdown(data: Dict[str, Any]) -> str:
    mode = data.get("options", {}).get("markdown_mode", DEFAULT_MARKDOWN_MODE)
    if mode == "compact":
        return render_compact_markdown(data)
    if mode in ("smart", "rbd_smart"):
        return render_compact_markdown(data, smart=True)
    if mode in ("attributes", "ultra"):  # "ultra" is the legacy name of attribute mode
        return render_ultra_markdown(data)

    lines: List[str] = []
    lines.append("# Houdini Scene Export%s" % _houdini_version_suffix(data))
    lines.append("")
    lines.append("- Connection notation: `A to B` means A is connected to B.")
    lines.append("")

    node_info = _compact_node_info(data.get("nodes", []))
    lines.extend(_render_node_tree(data.get("nodes", [])))
    lines.extend(_render_connections(data.get("connections", []), node_info))
    lines.extend(_render_code_blocks(data.get("code_blocks", [])))
    lines.extend(_render_nodes(data.get("nodes", [])))
    lines.extend(_render_hda_definitions(data.get("hda_definitions", [])))
    lines.extend(_render_errors(data.get("errors", [])))
    lines.extend(_llm_footer_lines(data))
    return "\n".join(lines).rstrip() + "\n"


def _render_node_tree(nodes: Sequence[Dict[str, Any]]) -> List[str]:
    lines = ["## Node Tree", ""]
    for node in sorted(nodes, key=lambda row: str(row.get("path", ""))):
        path = str(node.get("path"))
        depth = max(0, path.count("/") - 1)
        indent = "  " * depth
        node_type = node.get("type", {}).get("name_with_category") or node.get("type", {}).get("name")
        lines.append("%s- `%s`  type=`%s`" % (indent, path, node_type))
    lines.append("")
    return lines


def _render_connections(connections: Sequence[Dict[str, Any]], node_info: Optional[Dict[str, Dict[str, Any]]] = None) -> List[str]:
    lines = ["## Connections", ""]
    if not connections:
        lines.append("(none)")
        lines.append("")
        return lines
    node_info = node_info or {}

    def annotate(path: Any) -> str:
        info = node_info.get(str(path))
        if info is None or _compact_name_matches_type(info.get("name"), info):
            return "`%s`" % path
        return "`%s` (%s)" % (path, info.get("type_label") or "?")

    for connection in connections:
        src = connection.get("source", {})
        dst = connection.get("target", {})
        src_port = src.get("output_name") or src.get("output_index")
        dst_port = dst.get("input_name") or dst.get("input_index")
        lines.append(
            "- %s[%s] to %s[%s]"
            % (
                annotate(src.get("item") or src.get("node")),
                src_port,
                annotate(dst.get("item") or dst.get("node")),
                dst_port,
            )
        )
        src_type = src.get("output_data_type")
        dst_type = dst.get("input_data_type")
        if src_type or dst_type:
            lines.append("  data_type: `%s` to `%s`" % (src_type, dst_type))
    lines.append("")
    return lines


def _render_code_blocks(blocks: Sequence[Dict[str, Any]]) -> List[str]:
    lines = ["## Code Blocks", ""]
    if not blocks:
        lines.append("(none detected)")
        lines.append("")
        return lines
    for index, block in enumerate(blocks, 1):
        text_record = block.get("text", {})
        text = text_record.get("text", "") if isinstance(text_record, dict) else ""
        language = block.get("language_guess") or "text"
        lines.append("### Code %d: `%s` `%s`" % (index, block.get("node_path"), block.get("parm_path")))
        lines.append("")
        lines.append("```%s" % language)
        lines.append(str(text).rstrip())
        lines.append("```")
        lines.append("")
    return lines


def _render_nodes(nodes: Sequence[Dict[str, Any]]) -> List[str]:
    lines = ["## Node Details", ""]
    for node in sorted(nodes, key=lambda row: str(row.get("path", ""))):
        node_type = node.get("type", {})
        lines.append("### `%s`" % node.get("path"))
        lines.append("")
        lines.append("- Type: `%s` (%s)" % (node_type.get("name_with_category") or node_type.get("name"), node_type.get("description")))
        lines.append("- Parent: `%s`" % node.get("parent_path"))
        flags = node.get("flags", {})
        enabled_flags = [key for key, value in flags.items() if value is True]
        if enabled_flags:
            lines.append("- Flags true: `%s`" % "`, `".join(enabled_flags))
        comment = node.get("comment")
        if comment:
            lines.append("- Comment: %s" % _inline_text(str(comment)))
        lines.extend(_render_packed_rig_tree(node.get("packed_rig_tree")))
        lines.extend(_render_node_endpoints("Inputs", node.get("inputs", [])))
        lines.extend(_render_node_endpoints("Outputs", node.get("outputs", [])))
        if node.get("geometry_summary"):
            lines.extend(_render_geometry_summary(node.get("geometry_summary", {})))
        lines.extend(_render_parameters(node.get("parameters", [])))
        lines.append("")
    return lines


def _render_geometry_summary(summary: Dict[str, Any]) -> List[str]:
    lines = []
    counts = summary.get("counts", {})
    lines.append(
        "- Geometry: points=`%s`, vertices=`%s`, primitives=`%s`"
        % (counts.get("points"), counts.get("vertices"), counts.get("primitives"))
    )
    attr_counts = summary.get("attribute_counts", {})
    if attr_counts:
        lines.append(
            "  - Attribute counts: point=`%s`, vertex=`%s`, primitive=`%s`, detail=`%s`"
            % (
                attr_counts.get("point", 0),
                attr_counts.get("vertex", 0),
                attr_counts.get("primitive", 0),
                attr_counts.get("global", 0),
            )
        )
    mode = summary.get("mode", {})
    if mode:
        lines.append(
            "  - Geometry export mode: node=`%s`, samples=`%s`, standard_attrs=`%s`, private_attrs=`%s`"
            % (
                mode.get("node_mode"),
                mode.get("sample_count"),
                mode.get("standard_attributes_included"),
                mode.get("private_attributes_included"),
            )
        )
    attributes = summary.get("attributes", {})
    for owner, title in (("point", "Point"), ("vertex", "Vertex"), ("primitive", "Primitive"), ("global", "Detail")):
        records = attributes.get(owner, []) if isinstance(attributes, dict) else []
        if not records:
            continue
        pieces = []
        for attrib in records:
            scope = attrib.get("scope")
            scope_suffix = "" if scope in (None, "public", "default") else ":%s" % scope
            pieces.append(
                "%s%s %s[%s]"
                % (
                    attrib.get("name"),
                    scope_suffix,
                    attrib.get("data_type"),
                    attrib.get("size"),
                )
            )
        lines.append("  - %s attributes: `%s`" % (title, "`, `".join(pieces)))
    groups = summary.get("groups", {})
    if isinstance(groups, dict):
        group_pieces = []
        for owner in ("point", "vertex", "primitive", "edge"):
            records = groups.get(owner, [])
            if records:
                group_pieces.append("%s=%s" % (owner, len(records)))
        if group_pieces:
            lines.append("  - Groups: `%s`" % "`, `".join(group_pieces))
    omitted = summary.get("omitted_standard_attributes", {})
    omitted_pieces = []
    if isinstance(omitted, dict):
        for owner in ("point", "vertex", "primitive", "global"):
            records = omitted.get(owner, [])
            if records:
                omitted_pieces.append("%s=%s" % (owner, ",".join(str(record.get("name")) for record in records)))
    if omitted_pieces:
        lines.append("  - Omitted standard attributes: `%s`" % "`, `".join(omitted_pieces))
    return lines


def _render_node_endpoints(label: str, endpoints: Sequence[Dict[str, Any]]) -> List[str]:
    if not endpoints:
        return []
    text = ", ".join("[%s]=`%s`" % (endpoint.get("index"), endpoint.get("path")) for endpoint in endpoints)
    return ["- %s: %s" % (label, text)]


def _render_parameters(parameters: Sequence[Dict[str, Any]]) -> List[str]:
    lines = []
    if not parameters:
        return lines
    lines.append("- Parameters:")
    for parm_tuple in parameters:
        template = parm_tuple.get("template", {})
        label = parm_tuple.get("label") or template.get("label")
        type_text = template.get("type") or template.get("class")
        value = _parameter_tuple_display_value(parm_tuple)
        rendered_value = _short_value(value)
        if template.get("menu_items") or template.get("menu_labels"):
            menu_label = _compact_menu_value_label(parm_tuple, _compact_parameter_scalar(parm_tuple))
            if menu_label is not None:
                rendered_value = "%s (menu label: `%s`)" % (rendered_value, menu_label)
        lines.append(
            "  - `%s` (%s, %s): %s"
            % (parm_tuple.get("name"), label, type_text, rendered_value)
        )
        for parm in parm_tuple.get("parms", []):
            expression = _parm_record_expression_source(parm)
            raw_value = parm.get("raw_value")
            unexpanded = parm.get("unexpanded_string")
            if expression:
                lines.append(
                    "    - `%s` expression: %s"
                    % (parm.get("name"), _markdown_inline_code(expression))
                )
            elif unexpanded and unexpanded != raw_value:
                lines.append(
                    "    - `%s` unexpanded: %s"
                    % (parm.get("name"), _markdown_inline_code(unexpanded))
                )
            lines.extend(_parameter_channel_detail_lines(parm, "    - ", include_source=False))
    return lines


def _parameter_tuple_display_value(parm_tuple: Dict[str, Any]) -> Any:
    has_expression, expression_value = _parameter_tuple_expression_value(parm_tuple)
    if has_expression:
        return expression_value
    value = parm_tuple.get("values")
    if value is not None:
        return value
    values = []
    for parm in parm_tuple.get("parms", []):
        for key in ("expression", "unexpanded_string", "raw_value", "evaluated_value"):
            candidate = parm.get(key)
            if candidate is not None:
                values.append(candidate)
                break
    if not values:
        return None
    if len(values) == 1:
        return values[0]
    return values


def _short_value(value: Any, limit: int = 240) -> str:
    if value is None:
        return "`none`"
    text = json.dumps(value, ensure_ascii=False, sort_keys=True) if not isinstance(value, str) else value
    text = text.replace("\n", "\\n")
    if len(text) > limit:
        return "`%s...`" % text[:limit]
    return "`%s`" % text


def _inline_text(text: str, limit: int = 500) -> str:
    text = text.replace("\n", "\\n")
    if len(text) > limit:
        text = text[:limit] + "..."
    return text


def _render_hda_definitions(definitions: Sequence[Dict[str, Any]]) -> List[str]:
    lines = ["## HDA Definitions", ""]
    if not definitions:
        lines.append("(none)")
        lines.append("")
        return lines
    for definition in definitions:
        lines.append("### `%s`" % definition.get("key"))
        lines.append("")
        if definition.get("library_file_path"):
            lines.append("- Library: `%s`" % definition.get("library_file_path"))
        lines.append("- Sections included: `%s`" % definition.get("sections_included"))
        if definition.get("sections_skipped_reason"):
            lines.append("- Skipped reason: %s" % definition.get("sections_skipped_reason"))
        section_names = definition.get("section_names")
        if section_names:
            lines.append("- Section names: `%s`" % "`, `".join(section_names))
        for section in definition.get("sections", []):
            lines.append("- Section `%s` size=`%s` sha256=`%s`" % (section.get("name"), section.get("size"), section.get("sha256")))
            contents = section.get("contents")
            if isinstance(contents, dict) and contents.get("text"):
                language = _language_from_section_name(str(section.get("name") or ""))
                lines.append("")
                lines.append("```%s" % language)
                lines.append(str(contents.get("text")).rstrip())
                lines.append("```")
                lines.append("")
    lines.append("")
    return lines


def _language_from_section_name(name: str) -> str:
    lower = name.lower()
    if "python" in lower:
        return "python"
    if "vex" in lower or "vfl" in lower:
        return "c"
    if "dialog" in lower:
        return "text"
    return "text"


def _render_errors(errors: Sequence[Dict[str, Any]]) -> List[str]:
    lines = ["## Export Errors", ""]
    if not errors:
        lines.append("(none)")
        lines.append("")
        return lines
    for error in errors:
        lines.append("- `%s`: %s: %s" % (error.get("context"), error.get("error_type"), error.get("message")))
    lines.append("")
    return lines


def default_output_base() -> str:
    if hou is None:
        base_dir = os.getcwd()
        hip_name = "houdini_scene"
    else:
        hip_dir = hou.getenv("HIP") or os.getcwd()
        hip_path = hou.hipFile.path()
        hip_name = os.path.splitext(os.path.basename(hip_path or "untitled"))[0] or "untitled"
        base_dir = hip_dir if os.path.isdir(hip_dir) else os.getcwd()
    stamp = _datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    return os.path.join(base_dir, "%s_scene_text_%s" % (_sanitize_filename(hip_name), stamp))


def resolve_output_paths(output: Optional[str], output_format: str) -> Dict[str, str]:
    base = output or default_output_base()
    if os.path.isdir(base):
        base = os.path.join(base, os.path.basename(default_output_base()))

    root, ext = os.path.splitext(base)
    paths: Dict[str, str] = {}
    if output_format in ("markdown", "both"):
        paths["markdown"] = base if ext.lower() in (".md", ".markdown") and output_format == "markdown" else root + ".md"
    if output_format in ("json", "both"):
        paths["json"] = base if ext.lower() == ".json" and output_format == "json" else root + ".json"
    return paths


def export_current_scene(
    output: Optional[str] = None,
    output_format: str = "markdown",
    root_paths: Optional[Sequence[str]] = None,
    node_paths: Optional[Sequence[str]] = None,
    include_hidden_parms: bool = False,
    changed_only: bool = False,
    evaluate_parameters: bool = DEFAULT_EVALUATE_PARAMETERS,
    include_node_status: bool = False,
    include_parameter_state: bool = False,
    recurse_locked_nodes: bool = False,
    sync_delayed_definitions: bool = False,
    hda_section_mode: str = "none",
    max_text_chars: int = DEFAULT_MAX_TEXT_CHARS,
    markdown_mode: str = DEFAULT_MARKDOWN_MODE,
    include_geometry_summary: bool = False,
    geometry_sample_count: int = DEFAULT_GEOMETRY_SAMPLE_COUNT,
    geometry_node_mode: str = DEFAULT_GEOMETRY_NODE_MODE,
    include_private_attributes: bool = False,
    include_standard_attributes: bool = False,
    include_packed_rig_trees: bool = DEFAULT_INCLUDE_PACKED_RIG_TREES,
    include_bypassed_nodes: bool = DEFAULT_INCLUDE_BYPASSED_NODES,
    include_scene_paths: bool = DEFAULT_INCLUDE_SCENE_PATHS,
    include_network_items: bool = False,
    temporary_frame: Optional[float] = None,
) -> Dict[str, str]:
    if markdown_mode in ("smart", "rbd_smart"):
        # The mode is defined by the Parameter Pane's evaluated Hide When /
        # Disable When state and live dynamic menus, so state capture is not
        # optional even if the corresponding advanced checkbox is off.
        include_parameter_state = True
    if markdown_mode in ("attributes", "ultra"):
        # Attribute mode ("ultra" is its legacy name) dumps geometry attributes:
        # it needs cooked geometry and sample values.
        include_geometry_summary = True
        geometry_node_mode = "all"
        include_standard_attributes = True
        if geometry_sample_count == 0:
            geometry_sample_count = DEFAULT_ULTRA_SAMPLE_COUNT
    exporter = HoudiniSceneExporter(
        root_paths=root_paths,
        node_paths=node_paths,
        include_hidden_parms=include_hidden_parms,
        changed_only=changed_only,
        evaluate_parameters=evaluate_parameters,
        include_node_status=include_node_status,
        include_parameter_state=include_parameter_state,
        recurse_locked_nodes=recurse_locked_nodes,
        sync_delayed_definitions=sync_delayed_definitions,
        hda_section_mode=hda_section_mode,
        max_text_chars=max_text_chars,
        include_geometry_summary=include_geometry_summary,
        geometry_sample_count=geometry_sample_count,
        geometry_node_mode=geometry_node_mode,
        include_private_attributes=include_private_attributes,
        include_standard_attributes=include_standard_attributes,
        include_packed_rig_trees=include_packed_rig_trees,
        include_bypassed_nodes=include_bypassed_nodes,
        include_scene_paths=include_scene_paths,
        include_network_items=include_network_items,
        temporary_frame=temporary_frame,
    )
    data = exporter.export()
    data.setdefault("options", {})["markdown_mode"] = markdown_mode
    paths = resolve_output_paths(output, output_format)
    for path in paths.values():
        parent = os.path.dirname(os.path.abspath(path))
        if parent and not os.path.isdir(parent):
            os.makedirs(parent)
    if "json" in paths:
        _json_dump(data, paths["json"])
    if "markdown" in paths:
        _write_text(render_markdown(data), paths["markdown"])
    return paths


def _houdini_ui_available() -> bool:
    if hou is None:
        return False
    is_ui_available = getattr(hou, "isUIAvailable", None)
    if callable(is_ui_available):
        try:
            return bool(is_ui_available())
        except Exception:
            return False
    return False


def _import_qt() -> Tuple[Any, Any]:
    for package_name in ("PySide6", "PySide2"):
        try:
            module = __import__(package_name, fromlist=["QtCore", "QtWidgets"])
            return module.QtCore, module.QtWidgets
        except ImportError:
            continue
    raise RuntimeError("PySide6/PySide2 is not available. Run this UI inside Houdini's Python environment.")


def _qt_parent_window() -> Any:
    if hou is None:
        return None
    qt_module = getattr(hou, "qt", None)
    main_window = getattr(qt_module, "mainWindow", None) if qt_module is not None else None
    if callable(main_window):
        try:
            return main_window()
        except Exception:
            return None
    return None


def _combo_value(combo: Any) -> str:
    value = combo.currentData()
    if value is None:
        value = combo.currentText()
    return str(value)


def _set_combo_value(combo: Any, value: str) -> None:
    index = combo.findData(value)
    if index < 0:
        index = combo.findText(value)
    if index >= 0:
        combo.setCurrentIndex(index)


def _message_box_constant(message_box_class: Any, old_name: str, enum_name: str) -> Any:
    value = getattr(message_box_class, old_name, None)
    if value is not None:
        return value
    for enum_container_name in ("StandardButton", "ButtonRole"):
        enum_container = getattr(message_box_class, enum_container_name, None)
        value = getattr(enum_container, enum_name, None) if enum_container is not None else None
        if value is not None:
            return value
    return None


def _qt_constant(container: Any, old_name: str, enum_container_name: str, enum_name: str) -> Any:
    value = getattr(container, old_name, None)
    if value is not None:
        return value
    enum_container = getattr(container, enum_container_name, None)
    return getattr(enum_container, enum_name, None) if enum_container is not None else None


def _parse_root_paths(text: str) -> List[str]:
    roots = [part.strip() for part in re.split(r"[,;\n]+", text) if part.strip()]
    return roots or ["/"]


def _open_output_location(paths: Dict[str, str]) -> None:
    if not paths:
        return
    first_path = next(iter(paths.values()))
    folder = os.path.dirname(os.path.abspath(first_path))
    if sys.platform.startswith("win"):
        os.startfile(folder)  # type: ignore[attr-defined]


class HoudiniSceneExportDialog:
    def __init__(self, parent: Any = None) -> None:
        self.QtCore, self.QtWidgets = _import_qt()
        self.dialog = self.QtWidgets.QDialog(parent)
        self.dialog.setWindowTitle("Houdini Scene To Text %s" % SCHEMA_VERSION)
        self.dialog.setMinimumWidth(680)
        self._build_ui()

    def _build_ui(self) -> None:
        QtWidgets = self.QtWidgets
        layout = QtWidgets.QVBoxLayout(self.dialog)

        note = QtWidgets.QLabel(
            "標準設定では現在フレーム1枚だけパラメータを評価します。"
            "通常の SOP アトリビュート取得やノード状態問い合わせは行いません。"
            "パック済みリグの候補ノードは階層確認のため cook される場合があります。"
        )
        note.setWordWrap(True)
        layout.addWidget(note)

        output_group = QtWidgets.QGroupBox("出力")
        output_layout = QtWidgets.QFormLayout(output_group)
        self.output_edit = QtWidgets.QLineEdit(default_output_base())
        browse_button = QtWidgets.QPushButton("参照...")
        browse_button.clicked.connect(self._browse_output)
        output_row = QtWidgets.QHBoxLayout()
        output_row.addWidget(self.output_edit, 1)
        output_row.addWidget(browse_button)
        output_layout.addRow("出力先", output_row)
        layout.addWidget(output_group)

        scope_group = QtWidgets.QGroupBox("対象")
        scope_layout = QtWidgets.QFormLayout(scope_group)
        self.roots_edit = QtWidgets.QLineEdit("/")
        scope_layout.addRow("ルート", self.roots_edit)
        self.selected_check = QtWidgets.QCheckBox("選択中ノードだけを書き出す（子ノードは含めない）")
        scope_layout.addRow("", self.selected_check)
        layout.addWidget(scope_group)

        advanced_section, advanced_layout = self._collapsible_section("詳細設定", expanded=False)

        format_group = QtWidgets.QGroupBox("形式")
        format_layout = QtWidgets.QFormLayout(format_group)
        self.format_combo = QtWidgets.QComboBox()
        for label, value in (("Markdown", "markdown"), ("Markdown + JSON", "both"), ("JSON", "json")):
            self.format_combo.addItem(label, value)
        _set_combo_value(self.format_combo, "markdown")
        format_layout.addRow("形式", self.format_combo)
        self.markdown_mode_combo = QtWidgets.QComboBox()
        for label, value in (
            ("コンパクト", "compact"),
            ("スマートモード（実験的）", "smart"),
            ("詳細", "verbose"),
            ("アトリビュート（選択ノードの属性値・cookします）", "attributes"),
        ):
            self.markdown_mode_combo.addItem(label, value)
        _set_combo_value(self.markdown_mode_combo, DEFAULT_MARKDOWN_MODE)
        format_layout.addRow("Markdown", self.markdown_mode_combo)
        self.include_scene_paths_check = QtWidgets.QCheckBox("HIP / HDA ファイルパスも含める")
        self.include_scene_paths_check.setChecked(DEFAULT_INCLUDE_SCENE_PATHS)
        format_layout.addRow("", self.include_scene_paths_check)
        advanced_layout.addWidget(format_group)

        parm_group = QtWidgets.QGroupBox("パラメータ / HDA")
        parm_layout = QtWidgets.QFormLayout(parm_group)
        self.include_hidden_check = QtWidgets.QCheckBox("隠しパラメータも含める")
        self.include_hidden_check.setChecked(False)
        parm_layout.addRow("", self.include_hidden_check)
        self.include_bypassed_check = QtWidgets.QCheckBox("バイパスノードも含める")
        self.include_bypassed_check.setChecked(DEFAULT_INCLUDE_BYPASSED_NODES)
        parm_layout.addRow("", self.include_bypassed_check)
        self.include_network_items_check = QtWidgets.QCheckBox("付箋/ネットワークボックス/ドットも記録する（既定はドットを直結扱いにして省略）")
        self.include_network_items_check.setChecked(False)
        parm_layout.addRow("", self.include_network_items_check)
        self.changed_only_check = QtWidgets.QCheckBox("デフォルトから変わったパラメータだけにする（状態問い合わせを行います）")
        parm_layout.addRow("", self.changed_only_check)
        self.evaluate_parameters_check = QtWidgets.QCheckBox("現在フレームのパラメータを評価する")
        self.evaluate_parameters_check.setChecked(DEFAULT_EVALUATE_PARAMETERS)
        parm_layout.addRow("", self.evaluate_parameters_check)
        self.include_node_status_check = QtWidgets.QCheckBox("ノードのエラー/警告/メッセージも取得する（cook する場合があります）")
        parm_layout.addRow("", self.include_node_status_check)
        self.include_parameter_state_check = QtWidgets.QCheckBox("パラメータのデフォルト/無効/時間依存状態も取得する（cook する場合があります）")
        parm_layout.addRow("", self.include_parameter_state_check)
        self.recurse_locked_check = QtWidgets.QCheckBox("Locked HDA の中も見る")
        self.recurse_locked_check.setChecked(False)
        parm_layout.addRow("", self.recurse_locked_check)
        self.sync_delayed_check = QtWidgets.QCheckBox("遅延ロードされた HDA 定義を同期する")
        self.sync_delayed_check.setChecked(False)
        parm_layout.addRow("", self.sync_delayed_check)
        self.hda_section_combo = QtWidgets.QComboBox()
        for label, value in (("Scene HDA sections", "scene"), ("All HDA sections", "all"), ("No HDA sections", "none")):
            self.hda_section_combo.addItem(label, value)
        _set_combo_value(self.hda_section_combo, "none")
        parm_layout.addRow("HDA セクション", self.hda_section_combo)
        self.max_text_spin = QtWidgets.QSpinBox()
        self.max_text_spin.setRange(0, 2_000_000_000)
        self.max_text_spin.setValue(DEFAULT_MAX_TEXT_CHARS)
        self.max_text_spin.setSingleStep(10_000)
        parm_layout.addRow("文字数上限", self.max_text_spin)
        frame_row = QtWidgets.QHBoxLayout()
        self.temporary_frame_check = QtWidgets.QCheckBox("別フレーム1枚へ移動して書き出す")
        self.temporary_frame_spin = QtWidgets.QDoubleSpinBox()
        self.temporary_frame_spin.setRange(-1_000_000.0, 1_000_000.0)
        self.temporary_frame_spin.setDecimals(3)
        self.temporary_frame_spin.setValue(float(hou.frame()) if hou is not None else 1.0)
        self.temporary_frame_spin.setEnabled(False)
        self.temporary_frame_check.toggled.connect(self.temporary_frame_spin.setEnabled)
        frame_row.addWidget(self.temporary_frame_check)
        frame_row.addWidget(self.temporary_frame_spin)
        parm_layout.addRow("cook確認フレーム", frame_row)
        advanced_layout.addWidget(parm_group)

        geo_group = QtWidgets.QGroupBox("ジオメトリ / アトリビュート")
        geo_layout = QtWidgets.QFormLayout(geo_group)
        self.geometry_check = QtWidgets.QCheckBox("SOP ジオメトリを cook して属性情報を取得する")
        geo_layout.addRow("", self.geometry_check)
        self.geometry_node_combo = QtWidgets.QComboBox()
        for label, value in (("重要ノードだけ", "important"), ("全SOPノード", "all"), ("取得しない", "none")):
            self.geometry_node_combo.addItem(label, value)
        _set_combo_value(self.geometry_node_combo, DEFAULT_GEOMETRY_NODE_MODE)
        geo_layout.addRow("対象SOP", self.geometry_node_combo)
        self.geometry_sample_spin = QtWidgets.QSpinBox()
        self.geometry_sample_spin.setRange(-1, 1_000_000)
        self.geometry_sample_spin.setValue(DEFAULT_GEOMETRY_SAMPLE_COUNT)
        geo_layout.addRow("属性値サンプル数", self.geometry_sample_spin)
        self.standard_attrs_check = QtWidgets.QCheckBox("P / N / uv / Cd などの定番属性も含める")
        geo_layout.addRow("", self.standard_attrs_check)
        self.private_attrs_check = QtWidgets.QCheckBox("private 属性も含める")
        geo_layout.addRow("", self.private_attrs_check)
        self.packed_rig_trees_check = QtWidgets.QCheckBox("パック済みキャラクターのリグツリーを含める")
        self.packed_rig_trees_check.setChecked(DEFAULT_INCLUDE_PACKED_RIG_TREES)
        geo_layout.addRow("", self.packed_rig_trees_check)
        advanced_layout.addWidget(geo_group)
        layout.addWidget(advanced_section)

        self.status_label = QtWidgets.QLabel("")
        self.status_label.setWordWrap(True)
        layout.addWidget(self.status_label)

        button_row = QtWidgets.QHBoxLayout()
        button_row.addStretch(1)
        self.export_button = QtWidgets.QPushButton("書き出す")
        self.export_button.clicked.connect(self._export)
        cancel_button = QtWidgets.QPushButton("閉じる")
        cancel_button.clicked.connect(self.dialog.close)
        button_row.addWidget(self.export_button)
        button_row.addWidget(cancel_button)
        layout.addLayout(button_row)

        self.geometry_check.toggled.connect(self._update_geometry_controls)
        self._update_geometry_controls(False)

    def _collapsible_section(self, title: str, expanded: bool = False) -> Tuple[Any, Any]:
        QtWidgets = self.QtWidgets
        container = QtWidgets.QWidget()
        outer_layout = QtWidgets.QVBoxLayout(container)
        outer_layout.setContentsMargins(0, 0, 0, 0)

        toggle = QtWidgets.QToolButton()
        toggle.setText(title)
        toggle.setCheckable(True)
        toggle.setChecked(expanded)
        style = _qt_constant(self.QtCore.Qt, "ToolButtonTextBesideIcon", "ToolButtonStyle", "ToolButtonTextBesideIcon")
        if style is not None:
            toggle.setToolButtonStyle(style)

        content = QtWidgets.QWidget()
        content_layout = QtWidgets.QVBoxLayout(content)
        content_layout.setContentsMargins(18, 4, 0, 0)
        content.setVisible(expanded)

        right_arrow = _qt_constant(self.QtCore.Qt, "RightArrow", "ArrowType", "RightArrow")
        down_arrow = _qt_constant(self.QtCore.Qt, "DownArrow", "ArrowType", "DownArrow")
        if right_arrow is not None and down_arrow is not None:
            toggle.setArrowType(down_arrow if expanded else right_arrow)

        def set_expanded(checked: bool) -> None:
            content.setVisible(checked)
            if right_arrow is not None and down_arrow is not None:
                toggle.setArrowType(down_arrow if checked else right_arrow)

        toggle.toggled.connect(set_expanded)
        outer_layout.addWidget(toggle)
        outer_layout.addWidget(content)
        return container, content_layout

    def _browse_output(self) -> None:
        QtWidgets = self.QtWidgets
        current = self.output_edit.text().strip() or default_output_base()
        path, _selected_filter = QtWidgets.QFileDialog.getSaveFileName(
            self.dialog,
            "出力先を選択",
            current,
            "Houdini Scene Text (*.md *.json);;All Files (*)",
        )
        if path:
            self.output_edit.setText(path)

    def _update_geometry_controls(self, enabled: bool) -> None:
        for widget in (
            self.geometry_node_combo,
            self.geometry_sample_spin,
            self.standard_attrs_check,
            self.private_attrs_check,
        ):
            widget.setEnabled(enabled)

    def _export_options(self) -> Dict[str, Any]:
        include_geometry = self.geometry_check.isChecked()
        geometry_node_mode = _combo_value(self.geometry_node_combo) if include_geometry else "none"
        return {
            "output": self.output_edit.text().strip() or None,
            "output_format": _combo_value(self.format_combo),
            "markdown_mode": _combo_value(self.markdown_mode_combo),
            "root_paths": _parse_root_paths(self.roots_edit.text()),
            "node_paths": None,
            "include_hidden_parms": self.include_hidden_check.isChecked(),
            "changed_only": self.changed_only_check.isChecked(),
            "evaluate_parameters": self.evaluate_parameters_check.isChecked(),
            "include_node_status": self.include_node_status_check.isChecked(),
            "include_parameter_state": self.include_parameter_state_check.isChecked(),
            "recurse_locked_nodes": self.recurse_locked_check.isChecked(),
            "sync_delayed_definitions": self.sync_delayed_check.isChecked(),
            "hda_section_mode": _combo_value(self.hda_section_combo),
            "max_text_chars": self.max_text_spin.value(),
            "include_geometry_summary": include_geometry,
            "geometry_sample_count": self.geometry_sample_spin.value(),
            "geometry_node_mode": geometry_node_mode,
            "include_private_attributes": self.private_attrs_check.isChecked(),
            "include_standard_attributes": self.standard_attrs_check.isChecked(),
            "include_packed_rig_trees": self.packed_rig_trees_check.isChecked(),
            "include_bypassed_nodes": self.include_bypassed_check.isChecked(),
            "include_network_items": self.include_network_items_check.isChecked(),
            "include_scene_paths": self.include_scene_paths_check.isChecked(),
            "temporary_frame": self.temporary_frame_spin.value() if self.temporary_frame_check.isChecked() else None,
        }

    def _export(self) -> None:
        QtWidgets = self.QtWidgets
        options = self._export_options()
        if self.selected_check.isChecked():
            selected = list(hou.selectedNodes()) if hou is not None else []
            if not selected:
                QtWidgets.QMessageBox.warning(self.dialog, "Houdini Scene To Text", "選択中のノードがありません。")
                return
            options["node_paths"] = [node.path() for node in selected]

        cook_sensitive_reasons = []
        if options["markdown_mode"] in ("attributes", "ultra"):
            cook_sensitive_reasons.append("アトリビュートモード（属性値の取得）")
        elif options["include_geometry_summary"]:
            cook_sensitive_reasons.append("ジオメトリ/アトリビュート取得")
        if options["changed_only"]:
            cook_sensitive_reasons.append("デフォルト差分判定")
        if options["include_node_status"]:
            cook_sensitive_reasons.append("ノード状態取得")
        if options["include_parameter_state"]:
            cook_sensitive_reasons.append("パラメータ状態取得")
        current_frame = float(hou.frame()) if hou is not None else None
        if options["temporary_frame"] is not None and (current_frame is None or abs(float(options["temporary_frame"]) - current_frame) > 1e-6):
            cook_sensitive_reasons.append("一時フレーム移動")
        if cook_sensitive_reasons:
            yes_button = _message_box_constant(QtWidgets.QMessageBox, "Yes", "Yes")
            no_button = _message_box_constant(QtWidgets.QMessageBox, "No", "No")
            response = QtWidgets.QMessageBox.question(
                self.dialog,
                "cook の確認",
                "次の設定により、DOP/SOP/TOP/ROP が cook される可能性があります:\n"
                + "\n".join("- " + reason for reason in cook_sensitive_reasons)
                + "\n\n続行しますか？",
                yes_button | no_button,
                no_button,
            )
            if response != yes_button:
                return

        self.export_button.setEnabled(False)
        self.status_label.setText("書き出し中...")
        wait_cursor = _qt_constant(self.QtCore.Qt, "WaitCursor", "CursorShape", "WaitCursor")
        if wait_cursor is not None:
            QtWidgets.QApplication.setOverrideCursor(wait_cursor)
        QtWidgets.QApplication.processEvents()
        try:
            paths = export_current_scene(**options)
        except Exception as exc:
            traceback.print_exc()
            QtWidgets.QMessageBox.critical(self.dialog, "書き出し失敗", "%s: %s" % (exc.__class__.__name__, exc))
            self.status_label.setText("書き出しに失敗しました。")
            return
        finally:
            if wait_cursor is not None:
                QtWidgets.QApplication.restoreOverrideCursor()
            self.export_button.setEnabled(True)

        message = "書き出しました:\n" + "\n".join("%s: %s" % (kind, path) for kind, path in paths.items())
        self.status_label.setText(message)
        box = QtWidgets.QMessageBox(self.dialog)
        box.setWindowTitle("書き出し完了")
        box.setText(message)
        action_role = _message_box_constant(QtWidgets.QMessageBox, "ActionRole", "ActionRole")
        ok_button = _message_box_constant(QtWidgets.QMessageBox, "Ok", "Ok")
        open_button = box.addButton("フォルダを開く", action_role)
        box.addButton(ok_button)
        exec_method = getattr(box, "exec", None) or getattr(box, "exec_", None)
        if callable(exec_method):
            exec_method()
        if box.clickedButton() == open_button:
            _open_output_location(paths)

    def show(self) -> None:
        self.dialog.show()
        self.dialog.raise_()
        self.dialog.activateWindow()


_EXPORT_DIALOG: Optional[HoudiniSceneExportDialog] = None


def show_export_ui() -> Any:
    global _EXPORT_DIALOG
    _EXPORT_DIALOG = HoudiniSceneExportDialog(_qt_parent_window())
    _EXPORT_DIALOG.show()
    return _EXPORT_DIALOG.dialog


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Export Houdini nodes, connections, parameters, VEX/Python snippets, VOPs, TOPs, ROPs, subnets, and HDA sections to text.")
    parser.add_argument("hip_file", nargs="?", help="Optional .hip file to load before export when running in hython.")
    parser.add_argument("--ui", action="store_true", help="Show the PySide UI instead of running a command-line export.")
    parser.add_argument("--hip", dest="hip_file_option", default=None, help="Optional .hip file to load before export when running in hython.")
    parser.add_argument("--root", action="append", dest="roots", help="Root node path to export. Can be repeated. Default: /")
    parser.add_argument("--selected", action="store_true", help="Export selected nodes only, without recursing into their children.")
    parser.add_argument("--out", default=None, help="Output file base/path or directory. Default: $HIP/<hip>_scene_text_<timestamp>.")
    parser.add_argument("--format", choices=("markdown", "json", "both"), default="markdown", help="Output format.")
    parser.add_argument("--markdown-mode", choices=("compact", "smart", "rbd_smart", "verbose", "attributes", "ultra"), default=DEFAULT_MARKDOWN_MODE, help="Markdown detail level. smart renders node settings using current visible Parameter Pane labels and menu choices. rbd_smart is a deprecated alias for smart. attributes dumps geometry attribute/group values for the exported nodes (works with multiple selected nodes; forces geometry cooking). ultra is a deprecated alias for attributes.")
    parser.add_argument("--include-scene-paths", action="store_true", help="Include HIP and loaded HDA file paths. Off by default.")
    parser.add_argument("--changed-only", action="store_true", help="Only include parameters that are not at default values.")
    parser.add_argument("--evaluate-parameters", dest="evaluate_parameters", action="store_true", default=DEFAULT_EVALUATE_PARAMETERS, help="Evaluate parameter values on the current frame. On by default.")
    parser.add_argument("--no-evaluate-parameters", dest="evaluate_parameters", action="store_false", help="Do not evaluate parameter values; use raw/unexpanded input strings only.")
    parser.add_argument("--include-node-status", action="store_true", help="Include node errors/warnings/messages. Off by default because status queries can trigger cooks.")
    parser.add_argument("--include-parameter-state", action="store_true", help="Include parameter default/disabled/time-dependent state. Off by default because state queries can trigger cooks.")
    parser.add_argument("--temporary-frame", type=float, default=None, help="Temporarily switch to this frame during export, then restore the original frame. Use only when intentionally running cook-sensitive options.")
    parser.add_argument("--include-hidden-parms", action="store_true", help="Include hidden parameters. Off by default to keep exports compact.")
    parser.add_argument("--skip-hidden-parms", action="store_true", help="Deprecated compatibility option. Hidden parameters are skipped by default.")
    parser.add_argument("--include-bypassed-nodes", action="store_true", help="Include bypassed nodes. Off by default to keep exports focused on active flow.")
    parser.add_argument("--include-network-items", action="store_true", help="Include sticky notes, network boxes and network dots as records. Off by default; dots are always collapsed into direct connections.")
    parser.add_argument("--recurse-locked", action="store_true", help="Recurse into locked HDAs. Off by default to keep exports compact.")
    parser.add_argument("--sync-delayed", action="store_true", help="Force delayed HDA contents to load. Off by default.")
    parser.add_argument("--no-recurse-locked", action="store_true", help="Deprecated compatibility option. Locked HDA recursion is off by default.")
    parser.add_argument("--no-sync-delayed", action="store_true", help="Deprecated compatibility option. Delayed HDA sync is off by default.")
    parser.add_argument("--hda-section-mode", choices=("scene", "all", "none"), default="none", help="none skips HDA section bodies; scene includes embedded/non-HFS HDA sections; all includes built-in sections too.")
    parser.add_argument("--max-text-chars", type=int, default=DEFAULT_MAX_TEXT_CHARS, help="Per-field text limit. Use 0 for no truncation.")
    parser.add_argument("--include-geometry-summary", action="store_true", help="Cook important SOP geometry and include filtered attribute metadata. Off by default to avoid triggering heavy simulations.")
    parser.add_argument("--skip-geometry-summary", action="store_true", help="Do not cook SOP geometry or export geometry attributes.")
    parser.add_argument("--geometry-node-mode", choices=("important", "all", "none"), default=DEFAULT_GEOMETRY_NODE_MODE, help="Which SOP nodes should export geometry metadata. important exports display/render/selected/current and output/null/cache nodes.")
    parser.add_argument("--geometry-sample-count", type=int, default=DEFAULT_GEOMETRY_SAMPLE_COUNT, help="Number of point/vertex/primitive attribute sample values to include per attribute. Default 0 is metadata only. Use -1 to export all values.")
    parser.add_argument("--include-standard-attributes", action="store_true", help="Include common point/vertex attributes such as P, N, uv, Cd, v, pscale.")
    parser.add_argument("--include-private-attributes", action="store_true", help="Include private geometry attributes.")
    parser.add_argument("--skip-private-attributes", action="store_true", help="Deprecated compatibility option. Private attributes are skipped by default.")
    parser.add_argument("--include-packed-rig-trees", dest="include_packed_rig_trees", action="store_true", default=DEFAULT_INCLUDE_PACKED_RIG_TREES, help="Include packed character folder hierarchies from candidate SOP nodes. On by default.")
    parser.add_argument("--skip-packed-rig-trees", dest="include_packed_rig_trees", action="store_false", help="Do not query SOP geometry for packed character folder hierarchies.")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    if argv is None and _houdini_ui_available():
        show_export_ui()
        return 0

    parser = build_arg_parser()
    args, _unknown = parser.parse_known_args(argv)
    if hou is None:
        parser.error("hou module is not available. Run this inside Houdini 21 or with hython.")

    if args.ui:
        show_export_ui()
        return 0

    hip_file = args.hip_file_option or args.hip_file
    if hip_file:
        hou.hipFile.load(hip_file, suppress_save_prompt=True, ignore_load_warnings=True)

    include_geometry_summary = bool(args.include_geometry_summary)
    if args.skip_geometry_summary:
        include_geometry_summary = False
    geometry_node_mode = "none" if args.skip_geometry_summary else args.geometry_node_mode

    roots = args.roots or ["/"]
    node_paths = None
    if args.selected:
        selected = list(hou.selectedNodes())
        if selected:
            node_paths = [node.path() for node in selected]
        else:
            parser.error("--selected was used, but no Houdini nodes are selected.")

    try:
        paths = export_current_scene(
            output=args.out,
            output_format=args.format,
            markdown_mode=args.markdown_mode,
            root_paths=roots,
            node_paths=node_paths,
            include_hidden_parms=args.include_hidden_parms and not args.skip_hidden_parms,
            changed_only=args.changed_only,
            evaluate_parameters=args.evaluate_parameters,
            include_node_status=args.include_node_status,
            include_parameter_state=args.include_parameter_state,
            recurse_locked_nodes=args.recurse_locked and not args.no_recurse_locked,
            sync_delayed_definitions=args.sync_delayed and not args.no_sync_delayed,
            hda_section_mode=args.hda_section_mode,
            max_text_chars=args.max_text_chars,
            include_geometry_summary=include_geometry_summary,
            geometry_sample_count=args.geometry_sample_count,
            geometry_node_mode=geometry_node_mode,
            include_private_attributes=args.include_private_attributes and not args.skip_private_attributes,
            include_standard_attributes=args.include_standard_attributes,
            include_packed_rig_trees=args.include_packed_rig_trees,
            include_bypassed_nodes=args.include_bypassed_nodes,
            include_scene_paths=args.include_scene_paths,
            include_network_items=args.include_network_items,
            temporary_frame=args.temporary_frame,
        )
    except Exception:
        traceback.print_exc()
        return 1

    print("Houdini scene export written:")
    for kind, path in paths.items():
        print("  %s: %s" % (kind, path))
    return 0


if __name__ == "__main__":
    _exit_code = main()
    if not _houdini_ui_available():
        raise SystemExit(_exit_code)
elif _houdini_ui_available() and "__file__" not in globals() and not globals().get("_H2T_NO_AUTO_UI", False):
    show_export_ui()
