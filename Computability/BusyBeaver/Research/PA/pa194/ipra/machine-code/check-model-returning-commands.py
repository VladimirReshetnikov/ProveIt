#!/usr/bin/env python3
"""Rebuild the literal PA194 MP command and scheduler seam over staged dependencies."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


if len(sys.argv) != 5:
    raise SystemExit("usage: check-model-returning-commands.py REPO SOURCE_DIR FRESH_OUTPUT STAGES_FILE")
repo, src, out, manifest = (Path(arg).resolve() for arg in sys.argv[1:])
stages = [Path(line).resolve() for line in manifest.read_text().splitlines() if line]
if out.exists():
    raise SystemExit(f"Output already exists: {out}")
if any(not stage.is_dir() for stage in stages):
    raise SystemExit("A staged dependency directory is missing")
checks = {
    "PA194ModelMPDrain": ('runMany', 'frameDef', 'drain'),
    "PA194ModelCantorWalker": ('round', 'walk'),
    "PA194ModelMPTransfer": ('transfer',),
    "PA194ModelMPPair": ('triangleLoop', 'pair'),
    "PA194AXReaderAlgebra": ('outputH', 'outputD'),
    "PA194ModelAXReader": ('reader',),
    "PA194ShiftReaderRows": ('s11', 's24'),
    "PA194ShiftReaderAlgebra": ('output',),
    "PA194ModelShiftReader": ('rows', 'execute'),
    "PA194AXReaderRows131": ('s131', 's144'),
    "PA194AXReaderRows224": ('s224', 's237'),
    "PA194ModelAXReaderH": ('rows', 'execute'),
    "PA194ModelAXReaderD": ('rows', 'execute'),
    "PA194ShiftModelPreGuard": ('runToGuard',),
    "PA194ShiftModelGuardReturn": ('guardReturns',),
    "PA194ShiftModelReturn": ('shiftReturns', 'nextShiftFields', 'fromSchedulerFrame'),
    "PA194MPLiteralRows3554": ('s3554', 's3593'),
    "PA194MPLiteralRows3594": ('s3594', 's3620'),
    "PA194MPLiteralRows3621": ('s3621', 's3660'),
    "PA194ModelMPCopy": ('copy',),
    "PA194ModelMPCompare": ('comparePrefix', 'cleanup'),
    "PA194ModelMPFields": ('nextFields',),
    "PA194ModelMPPush": ('push',),
    "PA194ModelMPGuard": ('guard',),
    "PA194ModelMPImp": ('pop', 'build'),
    "PA194ModelMPField": ('field',),
    "PA194ModelMPCommand": ('command',),
    "PA194ModelMPSchedule": ('commandMatches',),
    "PA194ModelMPFromFrame": ('advance',),
}
inputs = {str(manifest): digest(manifest)}
for module in checks:
    source = src / f"{module}.lean"
    inputs[str(source)] = digest(source)
    for name in re.findall(r"^import ([\w.]+)$", source.read_text(), re.M):
        if name in checks:
            continue
        path = Path(*name.split(".")).with_suffix(".olean")
        found = [stage / path for stage in stages if (stage / path).is_file()]
        if not found:
            raise SystemExit(f"Missing direct import {name}")
        # LEAN_PATH order selects the direct import recorded in the receipt.
        inputs[str(found[0])] = digest(found[0])
out.mkdir()
lake_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=repo, text=True).strip()
env = os.environ | {"LEAN_PATH": ":".join(map(str, [out, *stages])) + ":" + lake_path}
for module, theorems in checks.items():
    log = out / f"{module}.log"
    with log.open("w") as dest:
        result = subprocess.run(
            ["lean", "-R", str(src), "-j1", "-M6000", "-o", str(out / f"{module}.olean"), str(src / f"{module}.lean")],
            cwd=repo, env=env, stdout=dest, stderr=subprocess.STDOUT,
        )
    report = log.read_text()
    print(report, end="")
    if result.returncode or "sorryAx" in report or "Lean.ofReduceBool" in report:
        raise SystemExit(f"{module} failed")
    for theorem in theorems:
        namespace = re.search(r"^namespace ([\w.]+)$", (src / f"{module}.lean").read_text(), re.M)[1]
        name = f"'{namespace}.{theorem}'"
        if not any(f"{name} {suffix}" in report for suffix in ("depends on axioms:", "does not depend on any axioms")):
            raise SystemExit(f"Missing axiom audit for {module}.{theorem}")
if any(digest(Path(name)) != sha for name, sha in inputs.items()):
    raise SystemExit("A recorded input changed during replay")
(out / "model-returning-commands-receipt.json").write_text(json.dumps(inputs, indent=2) + "\n")
print("PASS: exact PA194 MP and nonhalting SHIFT from one aligned frame to the next")
