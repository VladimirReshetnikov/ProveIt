#!/usr/bin/env python3
"""Run the release's finite checks; optionally record a receipt or check hashes."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
COMMIT = "3b201cdea32d2c816f5f3d20734051f25fd3ef14"
CHECKS = (
    "four_cell_compiler.py",
    "ordinary_start.py",
    "root_elimination.py",
    "root14_independent_audit.py",
    "quartic33.py",
)


def check_manifest() -> int:
    manifest = ROOT / "MANIFEST.sha256"
    failures = []
    count = 0
    for line in manifest.read_text(encoding="utf-8").splitlines():
        digest, relative = line.split("  ", 1)
        path = ROOT / relative
        if not path.is_file():
            failures.append(relative + ": missing")
        elif hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            failures.append(relative + ": hash mismatch")
        count += 1
    if failures:
        for failure in failures:
            print("FAIL " + failure, file=sys.stderr)
        return 1
    print(f"PASS release manifest: {count} files")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path,
                        help="write an aggregate JSON receipt at this path")
    parser.add_argument("--manifest-only", action="store_true",
                        help="check shipped file hashes without rerunning checks")
    args = parser.parse_args()
    if args.manifest_only:
        return check_manifest()

    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    results = []
    all_passed = True
    for name in CHECKS:
        start = time.monotonic()
        command = [sys.executable, "-B"]
        if sys.flags.optimize:
            command.append("-O")
        command.append(str(ROOT / "code" / name))
        run = subprocess.run(command, cwd=ROOT, env=env, text=True,
                             capture_output=True, check=False)
        elapsed = round(time.monotonic() - start, 3)
        passed = run.returncode == 0
        result = {
            "check": name,
            "status": "PASS" if passed else "FAIL",
            "returncode": run.returncode,
            "elapsed_seconds": elapsed,
            "stdout_sha256": hashlib.sha256(run.stdout.encode()).hexdigest(),
        }
        try:
            result["details"] = json.loads(run.stdout)
        except json.JSONDecodeError:
            result["stdout"] = run.stdout
        if run.stderr:
            result["stderr"] = run.stderr
        results.append(result)
        print(f"{result['status']} {name} ({elapsed:.3f}s)", flush=True)
        if not passed:
            all_passed = False
            print(run.stdout, file=sys.stderr)
            print(run.stderr, file=sys.stderr)

    receipt = {
        "status": "PASS" if all_passed else "FAIL",
        "source_commit": COMMIT,
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(),
        "optimized": bool(sys.flags.optimize),
        "checks": results,
        "scope": (
            "Exact algebra, finite machine and layout binding, and reproducible "
            "diagnostics. This is not a kernel proof of the compiler or the "
            "Pell lemmas, not a consistency proof, and not a K215 halting test."
        ),
    }
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(receipt, indent=2) + "\n",
                                encoding="utf-8")
    print("PASS all finite checks" if all_passed else "FAIL finite checks")
    return 0 if all_passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
