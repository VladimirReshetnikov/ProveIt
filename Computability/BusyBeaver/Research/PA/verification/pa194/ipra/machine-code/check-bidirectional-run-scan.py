#!/usr/bin/env python3
"""Rebuild the literal self-loop scan with the selected staged imports."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


if len(sys.argv) < 4:
    raise SystemExit("usage: check-bidirectional-run-scan.py REPO SOURCE_DIR FRESH_OUTPUT STAGE ...")
repo, src, out, *stages = (Path(arg).resolve() for arg in sys.argv[1:])
if out.exists():
    raise SystemExit(f"Output already exists: {out}")
if any(not stage.is_dir() for stage in stages):
    raise SystemExit("A staged dependency directory is missing")

module = "PA194BidirectionalRunScan"
source = src / f"{module}.lean"
inputs = {str(source): digest(source)}
for name in ("PA194SymbolicMove", "PA194GenericRightScan", "PA194ZeroRuns"):
    found = [stage / f"{name}.olean" for stage in stages if (stage / f"{name}.olean").is_file()]
    if not found:
        raise SystemExit(f"Missing direct import {name}")
    if len({digest(path) for path in found}) > 1:
        raise SystemExit(f"Conflicting direct import {name}")
    inputs[str(found[0])] = digest(found[0])

out.mkdir()
lake_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=repo, text=True).strip()
env = os.environ | {"LEAN_PATH": ":".join(map(str, [out, *stages])) + ":" + lake_path}
log = out / f"{module}.log"
with log.open("w") as dest:
    result = subprocess.run(
        ["lean", "-R", str(src), "-j1", "-M6000", "-o", str(out / f"{module}.olean"), str(source)],
        cwd=repo, env=env, stdout=dest, stderr=subprocess.STDOUT,
    )
report = log.read_text()
print(report, end="")
if result.returncode or "sorryAx" in report:
    raise SystemExit(f"{module} failed")
for theorem in ("scanStep", "partialScan", "fullScan"):
    if f"'{module}.{theorem}' depends on axioms:" not in report:
        raise SystemExit(f"Missing axiom audit for {theorem}")
if any(digest(Path(name)) != sha for name, sha in inputs.items()):
    raise SystemExit("A recorded input changed during replay")
(out / "bidirectional-run-scan-receipt.json").write_text(json.dumps(inputs, indent=2) + "\n")
print("PASS: bidirectional model-length literal self-loop scans")
