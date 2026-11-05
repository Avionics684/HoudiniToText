"""Packed Name Viewer: one-file installer; native VEX centers and text visualizer."""
import hou

TOOL_TAG = "houdinidebugscripts.packed_name_viewer.v5"
LABEL_ATTR = "__debug_rbd_name"
CENTER_VEX = r'''
function void label(vector pos; string value; int sourceprim) {
    int pt = addpoint(0, pos);
    setpointattrib(0, "name", pt, value);
    setpointattrib(0, "__debug_rbd_name", pt, value);
    setpointattrib(0, "debug_source_prim", pt, sourceprim);
    setpointgroup(0, "debug_name_centers", pt, 1);
}
string requested = chs("nameclass");
string owner = "";
if (requested != "point" && attribtype(1, "prim", "name") == 2 && attribsize(1, "prim", "name") == 1)
    owner = "primitive";
else if (requested != "primitive" && attribtype(1, "point", "name") == 2 && attribsize(1, "point", "name") == 1)
    owner = "point";
if (owner == "") error("primitive / point string name is required.");
vector offset = chv("labeloffset");
int count = 0;
for (int prim = 0; prim < nprimitives(1); prim++) {
    string type = primintrinsic(1, "typename", prim);
    if (find(type, "Packed") < 0) continue;
    string value = owner == "primitive" ? prim(1, "name", prim) : point(1, "name", primpoint(1, prim, 0));
    label(getbbox_center(1, itoa(prim)) + offset, value, prim);
    count++;
}
if (count == 0) {
    if (owner != "point") error("Packed primitives are required for primitive name.");
    for (int pt = 0; pt < npoints(1); pt++)
        label(point(1, "P", pt) + offset, point(1, "name", pt), -1);
}
setdetailattrib(0, "debug_name_owner", owner);
'''


def name_owner(geo, owner="auto"):
    if owner not in ("auto", "primitive", "point"):
        raise ValueError("owner must be auto, primitive, or point")
    for kind, attr in (("primitive", geo.findPrimAttrib("name")), ("point", geo.findPointAttrib("name"))):
        if owner in ("auto", kind) and attr is not None:
            if attr.dataType() == hou.attribData.String and attr.size() == 1 and not attr.isArrayType():
                return kind
    raise hou.Error("primitive / point に文字列 name がありません。")


def prepare_names(source, owner="auto"):
    """Create independent, unconnected points at packed bounding-box centers."""
    geo = source.geometry()
    if geo is None or source.errors():
        raise hou.Error("入力 SOP のエラーを確認してください。")
    name_owner(geo, owner)
    prepared = source.parent().createNode("attribwrangle", "PACKED_NAME_CENTERS")
    try:
        # Input 0 stays empty; input 1 is a read-only source for the VEX code.
        prepared.setInput(1, source)
        group = prepared.parmTemplateGroup()
        group.append(hou.StringParmTemplate("nameclass", "Name Class", 1,
            default_value=(owner,), menu_items=("auto", "primitive", "point"),
            menu_labels=("Auto (Primitive First)", "Primitive", "Point")))
        group.append(hou.FloatParmTemplate("labeloffset", "Label Offset", 3,
                                         default_value=(0.0, 0.0, 0.0)))
        prepared.setParmTemplateGroup(group)
        prepared.parm("class").set(0)  # Detail (only once)
        prepared.parm("snippet").set(CENTER_VEX)
        prepared.geometry()
        if prepared.errors():
            raise hou.Error(str(prepared.errors()))
    except Exception:
        prepared.destroy()
        raise
    return prepared


def create_viewer(source, owner="auto", activate=True):
    if not hou.isUIAvailable():
        raise hou.Error("Houdini GUI 内で実行してください。")
    if isinstance(source, hou.ObjNode):
        source = source.displayNode()
    if not isinstance(source, hou.SopNode):
        raise hou.Error("表示したい SOP を1つ選択してください。")
    tag = source.userData("debug_tool") or ""
    if tag == TOOL_TAG:
        if activate:
            source.setDisplayFlag(True)
            reference = source.parm("wirereference").evalAsNode()
            if reference is not None:
                reference.setTemplateFlag(bool(source.evalParm("showwire")))
            source.setCurrent(True, clear_all_selected=True)
        return source
    if tag.startswith("houdinidebugscripts.packed_name_viewer."):
        raise hou.Error("旧版ではなく元の SOP を選択してください。")
    geo = source.geometry()
    if geo is None or source.errors():
        raise hou.Error("入力 SOP のエラーを確認してください。")
    resolved = name_owner(geo, owner)
    values = geo.primStringAttribValues("name") if resolved == "primitive" else geo.pointStringAttribValues("name")
    if not any(x.strip() for x in values):
        raise hou.Error(resolved + " の name はすべて空です。")
    result = reference = None
    with hou.undos.group("Packed Name Viewer"):
        try:
            result = prepare_names(source, owner)
            result.setName("DEBUG_PACKED_NAME", unique_name=True)
            reference = source.parent().createNode("null", "PACKED_WIREFRAME_REFERENCE")
            reference.setInput(0, source)
            reference.setRenderFlag(False)
            result.setRenderFlag(False)
            result.setUserData("wire_reference", reference.path())
            controls = result.parmTemplateGroup()
            wire_path = hou.StringParmTemplate("wirereference", "Wireframe Reference", 1,
                default_value=(result.relativePathTo(reference),),
                string_type=hou.stringParmType.NodeReference)
            wire_path.hide(True)
            controls.append(wire_path)
            wire = hou.ToggleParmTemplate("showwire", "Show Piece Wireframe", default_value=True)
            wire.setScriptCallback("n = kwargs['node'].parm('wirereference').evalAsNode()\nif n is not None:\n    n.setTemplateFlag(bool(kwargs['node'].evalParm('showwire')))\n")
            wire.setScriptCallbackLanguage(hou.scriptLanguage.Python)
            controls.append(wire)
            result.setParmTemplateGroup(controls)
            result.setUserData("debug_tool", TOOL_TAG)
            # Match SideFX's own string-attribute visualizer initialization.
            api = hou.viewportVisualizers
            category = hou.viewportVisualizerCategory.Node
            viz = api.createVisualizer(api.type("vis_generic"), category, result)
            viz.setType(api.type("vis_marker"))
            viz.setName("debug_packed_name_v5")
            viz.setLabel("Packed Name")
            viz.setParm("attrib", LABEL_ATTR)
            # Keep menu/style defaults: do not write guessed types or indices.
            viz.setScope(hou.viewportVisualizerScope.NodeOnly)
            viz.setIsActiveWhenDisplayed(True)
            viz.setIsActiveWhenSelected(True)
            viz.setIsActiveWhenUnselected(True)
            viz.setIsActive(True)
            api.setIsCategoryActive(True, category, node=result)
            result.setPosition(source.position() + hou.Vector2(3, -1))
            reference.setPosition(source.position() + hou.Vector2(0, -1))
            result.setColor(hou.Color((0.15, 0.65, 0.75)))
            result.setComment("Packed Name\nVEX center labels + wireframe reference\nPoint group: debug_name_centers")
        except Exception:
            if result is not None:
                result.destroy()
            if reference is not None:
                reference.destroy()
            raise
        if activate:
            result.setDisplayFlag(True)
            reference.setTemplateFlag(True)
            result.setCurrent(True, clear_all_selected=True)
    return result


def run():
    selected = hou.selectedNodes()
    if len(selected) != 1:
        hou.ui.displayMessage("元の SOP ノードを1つ選択してください。")
        return
    try:
        create_viewer(selected[0])
    except (hou.Error, RuntimeError, ValueError) as error:
        hou.ui.displayMessage(str(error), title="Packed Name Viewer", severity=hou.severityType.Warning)


if __name__ == "__main__":
    run()
