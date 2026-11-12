#!/usr/bin/env python3
"""Rebuild reference modules and the normalization bridge.
Usage: python3 formal/check_lean.py /absolute/path/to/pinned/mathlib4
Requires Lean/Lake 4.32.0 on PATH and the two cached Mathlib dependencies.
"""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = "81a5d257c8e410db227a6665ed08f64fea08e997"


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    mathlib = Path(sys.argv[1]).resolve()
    rev = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=mathlib, text=True).strip()
    if rev != EXPECTED:
        raise SystemExit("Wrong Mathlib revision: " + rev)
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    if "version 4.32.0," not in version:
        raise SystemExit("Wrong Lean toolchain: " + version)
    build = ROOT / "build" / "lean"
    refs = build / "ConciseIPRA"
    refs.mkdir(parents=True, exist_ok=True)
    for source in (ROOT / "reference" / "ConciseIPRA").glob("*.lean"):
        shutil.copy2(source, refs / source.name)
    compat = refs / "OneContextOneIntro.lean"
    text = compat.read_text()
    old = "WPrf.eqSymm transported"
    if text.count(old) != 1:
        raise SystemExit("Inherited compatibility patch does not match")
    compat.write_text(text.replace(old, "WKernel.eqSymm transported"))
    for name in ["ZeroNormalization.lean", "ZeroNormalizationAxioms.lean"]:
        shutil.copy2(ROOT / "formal" / name, build / name)

    modules = {f.stem: f for f in refs.glob("*.lean")}
    order = []

    def add(name):
        if name in order:
            return
        for dep in re.findall(
                r"^import ConciseIPRA\.(\w+)", modules[name].read_text(), re.M):
            add(dep)
        order.append(name)

    for name in ["NativeBiInterpretation", "NativeOneIntro",
                 "OneContext", "OneContextOneIntro",
                 "OneContextBiInterpretation"]:
        add(name)
    files = [modules[name] for name in order]
    files += [build / "ZeroNormalization.lean",
              build / "ZeroNormalizationAxioms.lean"]
    env = os.environ.copy()
    env["LEAN_PATH"] = str(build) + (
        os.pathsep + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
    rows = []
    for path in files:
        process = subprocess.run(
            ["lake", "env", "lean", "--root=" + str(build),
             "-o", str(path.with_suffix(".olean")), str(path)],
            cwd=mathlib, env=env, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        rows.append({"module": str(path.relative_to(build)),
                     "exit_code": process.returncode, "output": process.stdout})
        print(path.name + ": " + ("OK" if process.returncode == 0 else "FAILED"),
              flush=True)
        if process.stdout:
            print(process.stdout, end="")
        (build / "compilation.json").write_text(
            json.dumps({"lean": version, "mathlib": rev, "modules": rows},
                       indent=2) + "\n")
        if process.returncode:
            raise SystemExit(process.returncode)
    (build / "axioms.log").write_text(rows[-1]["output"])
    print("All modules compiled; axiom audit saved under build/lean.")


if __name__ == "__main__":
    main()
