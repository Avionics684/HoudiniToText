"""Launch the Houdini Scene To Text UI inside Houdini."""

from __future__ import annotations

import runpy


tool = runpy.run_path(r"C:\Users\ponpa\Documents\houdinitotext\houdini_scene_to_text.py")
tool["show_export_ui"]()
