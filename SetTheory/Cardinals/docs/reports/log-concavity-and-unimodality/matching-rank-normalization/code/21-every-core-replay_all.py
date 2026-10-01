#!/usr/bin/env python3
"""Replay the exact supplementary checks and compare all recorded data."""
from pathlib import Path
import json, subprocess, sys
base=Path(__file__).resolve().parent
for name in ("verify_incidence","check_weighted_planes"):
    subprocess.run([sys.executable,"-O",str(base/(name+".py"))],check=True)
    observed=json.loads((base/(name+".json")).read_text())
    expected=json.loads((base.parent/"data"/(name+".json")).read_text())
    if observed!=expected:
        raise RuntimeError("Replay output differs: "+name)
print("Both exact replays match the packaged reference data.")

