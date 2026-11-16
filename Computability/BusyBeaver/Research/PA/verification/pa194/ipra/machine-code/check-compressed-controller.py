#!/usr/bin/env python3
"""Rebuild the folded instruction and controller-to-literal proof over staged dependencies."""
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
    raise SystemExit("usage: check-compressed-controller.py REPO SOURCE_DIR FRESH_OUTPUT STAGES_FILE")
repo, src, out, manifest = (Path(arg).resolve() for arg in sys.argv[1:])
stages = [Path(line).resolve() for line in manifest.read_text().splitlines() if line]
if out.exists():
    raise SystemExit(f"Output already exists: {out}")
if any(not stage.is_dir() for stage in stages):
    raise SystemExit("A staged dependency directory is missing")
checks = {
    "PA194FoldedCache": ("keys_match", "checkRows_sound"),
    "PA194FoldedCacheCorrect": ("cachedMachine_correct",),
    "PA194FoldedChecks": ("checked_at",),
    "PA194FoldedSourceContracts": ("atSite",),
    "PA194CompressedRootCode": ("indexedCorrect", "rootCodeCorrect"),
    "PA194CompressedSourceFrame": ("packedFileCodeCorrect", "sourceRootCodeCorrect"),
    "PA194CompressedSourceArgs": ("incrementRegisters", "updatedRegisters"),
    "PA194CompressedSourceOrbit": ("rootDef", "alignmentDef", "synchronize", "equivalent"),
    "PA194CompressedControllerStep": ("stepAt", "advance"),
    "PA194CompressedStartup": ("blankToRoot", "initialAligned"),
    "PA194CompressedLiteralController": ("endpoint",),
    "PA194CompressedNativeController": ("endpoint",),
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
        name = f"'{module}.{theorem}'"
        if not any(f"{name} {suffix}" in report for suffix in ("depends on axioms:", "does not depend on any axioms")):
            raise SystemExit(f"Missing axiom audit for {module}.{theorem}")
if any(digest(Path(name)) != sha for name, sha in inputs.items()):
    raise SystemExit("A recorded input changed during replay")
(out / "compressed-controller-receipt.json").write_text(json.dumps(inputs, indent=2) + "\n")
print("PASS: folded instruction decoding and conditional literal/controller endpoint")
