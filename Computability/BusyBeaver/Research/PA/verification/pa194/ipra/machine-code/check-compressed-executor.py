#!/usr/bin/env python3
"""Rebuild compressed tape and runtime semantics over staged dependencies."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


if len(sys.argv) < 5:
    raise SystemExit("usage: check-compressed-executor.py REPO SOURCE_DIR FRESH_OUTPUT STAGE ...")
repo, src, out, *stages = (Path(arg).resolve() for arg in sys.argv[1:])
if out.exists():
    raise SystemExit(f"Output already exists: {out}")
if any(not stage.is_dir() for stage in stages):
    raise SystemExit("A staged dependency directory is missing")
checks = {
    "PA194CompressedTape": ("transPositive", "peelRun", "removeEmptyRun", "rightRow", "leftRow"),
    "PA194CompressedExecutor": ("symbolicStep", "checkedRun"),
    "PA194FoldedRuntimeRows": ("agreement", "root_control", "terminal_control"),
}
inputs = {}
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
        if len({digest(candidate) for candidate in found}) > 1:
            raise SystemExit(f"Conflicting direct import {name}")
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
    if result.returncode or "sorryAx" in report:
        raise SystemExit(f"{module} failed")
    for theorem in theorems:
        name = f"'{module}.{theorem}'"
        if not any(f"{name} {suffix}" in report for suffix in ("depends on axioms:", "does not depend on any axioms")):
            raise SystemExit(f"Missing axiom audit for {module}.{theorem}")
if any(digest(Path(name)) != sha for name, sha in inputs.items()):
    raise SystemExit("A recorded input changed during replay")
(out / "compressed-executor-receipt.json").write_text(json.dumps(inputs, indent=2) + "\n")
print("PASS: model-length packed tape and compressed executor with explicit box contracts")
