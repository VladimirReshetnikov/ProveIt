#!/usr/bin/env python3
"""Replay standalone Lean kernels in an existing pinned Lake project.

No dependency downloads, production edits, or patch applications are made.
The optional receipt includes command outputs and elapsed durations; these
durations are not controlled before/after performance measurements.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import time


KERNELS = [
    "BaselineOrderRigidity.lean", "FiniteOrderRigidity.lean",
    "ControllerCastBaseline.lean", "ControllerCastReview.lean",
    "ControllerIntervalBaseline.lean", "ControllerIntervalIndependent.lean",
    "semantic_nonzero.lean", "SourceSelectionPositivity.lean",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", required=True, type=Path)
    parser.add_argument("--lake", default="lake", help="Pinned Lake executable")
    parser.add_argument("--output", default=Path("kernel-replay.json"), type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    version = subprocess.run([args.lake, "env", "lean", "--version"],
                             cwd=args.project, capture_output=True, text=True)
    if version.returncode or "version 4.32.0," not in version.stdout:
        raise SystemExit("Expected Lean 4.32.0: " + version.stdout + version.stderr)
    results = []
    for name in KERNELS:
        command = [args.lake, "env", "lean", str(root / "lean" / name)]
        start = time.monotonic()
        p = subprocess.run(command, cwd=args.project, text=True, capture_output=True)
        results.append({"file": name, "exit_code": p.returncode,
                        "elapsed_seconds": time.monotonic() - start,
                        "stdout": p.stdout, "stderr": p.stderr})
        print(name, "PASS" if p.returncode == 0 else "FAIL", flush=True)
        if p.returncode:
            print(p.stdout + p.stderr)
            break
    ok = len(results) == len(KERNELS) and all(p["exit_code"] == 0 for p in results)
    args.output.write_text(json.dumps({"scope": "standalone kernels, not full production integration",
                                      "version": version.stdout.strip(), "ok": ok,
                                      "results": results}, indent=2) + "\n")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
