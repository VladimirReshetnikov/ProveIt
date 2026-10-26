#!/usr/bin/env python3
"""Replay the standalone LTE prototype and its same-signature candidate.

Usage: python3 verify_lte.py /path/to/ProveIt
Requirements: the checkout's pinned Lean 4.32.0 and Mathlib dependencies are
installed; `lake` is on PATH. No source in the checkout is modified.
"""
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.32.0"
EXPECTED_MATHLIB = "81a5d257c8e410db227a6665ed08f64fea08e997"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("repo", type=Path)
    ap.add_argument("--inside-lake", action="store_true", help=argparse.SUPPRESS)
    args = ap.parse_args()
    repo = args.repo.resolve()
    if (repo / "lean-toolchain").read_text().strip() != EXPECTED_TOOLCHAIN:
        raise SystemExit("Unexpected Lean toolchain; use the pinned reviewed version.")
    manifest = json.loads((repo / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    if mathlib["rev"] != EXPECTED_MATHLIB:
        raise SystemExit("Unexpected Mathlib revision; use the pinned reviewed version.")
    if not args.inside_lake:
        subprocess.run(["lake", "env", sys.executable, str(Path(__file__).resolve()),
                        str(repo), "--inside-lake"], cwd=repo, check=True)
        return
    source_root = repo / "Computability/DiophantineConsistency/Lean"
    checks = source_root / "DiophantineConsistency/PrimePowerOrderChecks.lean"
    if not checks.exists():
        raise SystemExit("The maintained PrimePowerOrderChecks.lean file is absent.")
    commands = []
    with tempfile.TemporaryDirectory(prefix="proveit-lte-") as temp:
        out = Path(temp)
        (out / "DiophantineConsistency").mkdir()
        baseline = source_root / "DiophantineConsistency/PrimePowerOrder.lean"
        candidate_root = HERE / "candidate"
        candidate = candidate_root / "DiophantineConsistency/PrimePowerOrder.lean"
        commands = [
            ("standalone", ["lean", "--root=" + str(HERE), str(HERE / "FullLTESpectrum.lean")],
             os.environ.copy()),
            ("candidate", ["lean", "--root=" + str(candidate_root), str(candidate), "-o",
                           str(out / "DiophantineConsistency/PrimePowerOrder.olean")],
             os.environ.copy()),
        ]
        for label, command, environment in commands:
            print("Checking", label, flush=True)
            subprocess.run(command, cwd=repo, env=environment, check=True)
        env = os.environ.copy()
        env["LEAN_PATH"] = str(out) + os.pathsep + env.get("LEAN_PATH", "")
        print("Checking maintained PrimePowerOrderChecks.lean against candidate", flush=True)
        subprocess.run(["lean", "--root=" + str(source_root), str(checks)],
                       cwd=repo, env=env, check=True)
        print("PASS: standalone prototype, candidate module, and maintained checks.")


if __name__ == "__main__":
    main()
