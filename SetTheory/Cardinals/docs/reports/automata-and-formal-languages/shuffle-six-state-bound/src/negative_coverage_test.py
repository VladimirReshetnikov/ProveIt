#!/usr/bin/env python3
"""Ensure that omitting the sole three-row certificate is detected."""
from pathlib import Path
import json
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
lines = (root / "audit/verified_targets.tsv").read_text().splitlines()
with tempfile.TemporaryDirectory() as directory:
    path = Path(directory) / "missing.tsv"
    path.write_text("\n".join(line for line in lines if not line.startswith("3\t"))+"\n")
    proc = subprocess.run([str(root / "audit/coverage"),str(path)],capture_output=True,text=True)
if proc.returncode == 0 or "UNCOVERED family: m=3" not in proc.stderr:
    raise RuntimeError("missing-certificate test did not fail as expected")
out = {"result":"PASS", "omitted":"the sole three-row certificate", "checker_exit_status":proc.returncode,
       "diagnostic":proc.stderr.strip()}
(root / "audit/negative_coverage.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
