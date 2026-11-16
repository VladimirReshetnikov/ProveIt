#!/usr/bin/env python3
"""Rebuild the PA194 AX controller and literal/scheduler equivalence."""
from concurrent.futures import ThreadPoolExecutor
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
    raise SystemExit("usage: check-ax-controller.py REPO SOURCE_DIR FRESH_OUTPUT STAGES_FILE")
repo, src, out, manifest = (Path(arg).resolve() for arg in sys.argv[1:])
stages = [Path(line).resolve() for line in manifest.read_text().splitlines() if line]
if out.exists():
    raise SystemExit(f"Output already exists: {out}")
if any(not stage.is_dir() for stage in stages):
    raise SystemExit("A staged dependency directory is missing")
prefix = """
PA194ModelAXCopy PA194ModelAXCons PA194ModelAXConsAlgebra PA194ModelAXConsExecute PA194ModelAXReads PA194ModelAXPlan PA194ModelAXPlanPositive PA194AXGateRows PA194ModelAXCompare PA194ModelAXGate PA194ModelAXFields PA194ModelAXFromFrame PA194AXResultExpressions PA194AXModelSymbolic PA194AXModelValues PA194AXReturnReduction
""".split()
batches = [f"PA194ModelAXBatch{n:03}" for n in range(0, 251, 10)]
suffix = ["PA194ModelAXBound", "PA194ModelAXBody", "PA194LiteralSchedulerCorrectness"]
checks = {
    module: tuple(re.findall(r"^#print axioms (\w+)", (src / f"{module}.lean").read_text(), re.M))
    for module in [*prefix, *batches, *suffix]
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
def check(module):
    theorems = checks[module]
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
    print(f"PASS {module}", flush=True)

for module in prefix:
    check(module)
with ThreadPoolExecutor(max_workers=2) as workers:
    list(workers.map(check, batches))
for module in suffix:
    check(module)

if any(digest(Path(name)) != sha for name, sha in inputs.items()):
    raise SystemExit("A recorded input changed during replay")
(out / "ax-controller-receipt.json").write_text(json.dumps(inputs, indent=2) + "\n")
print("PASS: literal PA194 halting iff modeled scheduler halting")
