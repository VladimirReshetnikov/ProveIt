#!/usr/bin/env python3
"""Run all exact checks and compare their recorded outputs."""
from pathlib import Path
import subprocess,sys,json
here=Path(__file__).resolve().parent
for name in ("replay_certificate","verify_virtual_orbits","check_last_gap_quadratic"):
    subprocess.run([sys.executable,"-O",str(here/(name+".py"))],check=True)
    actual=json.loads((here/(name+".json")).read_text())
    expected=json.loads((here.parent/"data"/(name+".json")).read_text())
    if actual!=expected:raise RuntimeError("Reference output mismatch: "+name)
print("All three exact checks match the included reference records.")

