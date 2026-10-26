#!/usr/bin/env python3
"""Replay the isolated controller proof chain using an existing pinned Mathlib.

No network access is attempted. All required Mathlib .olean files must exist.
The exact production patch retains its original imports; this standalone
replay replaces the broad Mathlib.Tactic import by precise cached imports.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mathlib-root", required=True, type=Path)
    parser.add_argument("--lean-bin", required=True, type=Path,
                        help="Directory containing pinned lean and lake")
    parser.add_argument("--output", type=Path, default=Path("controller-validation.json"))
    args = parser.parse_args()
    here = Path(__file__).resolve().parents[1] / "overlays/controller-validation"
    env = os.environ.copy()
    env["PATH"] = str(args.lean_bin.resolve()) + os.pathsep + env.get("PATH", "")
    lean = args.lean_bin.resolve() / "lean"
    lake = args.lean_bin.resolve() / "lake"
    path = subprocess.check_output(
        [str(lake), "env", "printenv", "LEAN_PATH"],
        cwd=args.mathlib_root, env=env, text=True).strip()
    names = ["ControllerIntervalSums", "ControllerOrbitTransport",
             "ControllerAuxiliaryChoice", "ControllerResidueLift"]
    results = []
    with tempfile.TemporaryDirectory(prefix="controller-review-") as tmp:
        build = Path(tmp)
        module_dir = build / "DiophantineConsistency"
        module_dir.mkdir()
        for name in names:
            source = here / "controller_sources/after/DiophantineConsistency" / (name + ".lean")
            text = source.read_text()
            text = text.replace("import Mathlib.Tactic\n",
                                "import Mathlib.Algebra.BigOperators.Ring.Finset\n")
            (module_dir / (name + ".lean")).write_text(text)
            checks = here / "controller_sources/checks/DiophantineConsistency" / (name + "Checks.lean")
            (module_dir / (name + "Checks.lean")).write_text(
                "import Mathlib.Tactic.NormNum\nimport Mathlib.Tactic.NormNum.Prime\n" +
                checks.read_text())
        shutil.copy2(here / "controller_overlay/ControllerAudit.lean", build / "ControllerAudit.lean")
        env["LEAN_PATH"] = str(build) + os.pathsep + path
        commands = [(module_dir / (n + ".lean"), True) for n in names]
        commands += [(module_dir / (n + "Checks.lean"), False) for n in names]
        commands += [(build / "ControllerAudit.lean", False)]
        for source, produce_object in commands:
            cmd = [str(lean)]
            if produce_object:
                cmd += ["-o", str(source.with_suffix(".olean"))]
            cmd.append(str(source))
            start = time.monotonic()
            result = subprocess.run(cmd, cwd=build, env=env, text=True, capture_output=True)
            results.append({"module": source.stem, "exit_code": result.returncode,
                            "elapsed_seconds": time.monotonic() - start,
                            "output": result.stdout + result.stderr})
            print(source.stem, "PASS" if result.returncode == 0 else "FAIL", flush=True)
            if result.returncode:
                print(result.stdout + result.stderr)
                break
    args.output.write_text(json.dumps({"scope": "isolated source and client replay",
                                     "import_adaptation": "explicit minimal imports; patch unchanged",
                                     "checks": results}, indent=2) + "\n")
    return 0 if len(results) == 9 and all(r["exit_code"] == 0 for r in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
