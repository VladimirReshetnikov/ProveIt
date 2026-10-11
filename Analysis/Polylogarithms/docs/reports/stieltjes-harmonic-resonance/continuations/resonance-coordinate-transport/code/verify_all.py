#!/usr/bin/env python3
"""Run the three complete verification scripts, stopping at the first failure."""
from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
VERIFIERS = (
    "verify_dougall.py",
    "verify_nonlinear.py",
    "verify_transport.py",
)


def main() -> int:
    scripts = [PACKAGE_ROOT / "code" / name for name in VERIFIERS]
    for script in scripts:
        if not script.is_file():
            print(f"Missing verifier: {script}", file=sys.stderr, flush=True)
            return 2

    # The supplied scripts use assert for exact and numerical comparisons.
    # Do not allow inherited optimization settings to disable those checks.
    child_environment = os.environ.copy()
    child_environment.pop("PYTHONOPTIMIZE", None)

    for index, script in enumerate(scripts, start=1):
        print(f"[{index}/{len(scripts)}] Running {script.name}", flush=True)
        try:
            result = subprocess.run(
                [sys.executable, "-u", str(script)],
                cwd=PACKAGE_ROOT,
                env=child_environment,
                check=False,
            )
        except KeyboardInterrupt:
            print("Verification interrupted.", file=sys.stderr, flush=True)
            return 130
        except OSError as exc:
            print(f"Could not start {script.name}: {exc}", file=sys.stderr, flush=True)
            return 127
        if result.returncode:
            print(
                f"FAILED: {script.name} returned {result.returncode}; stopping.",
                file=sys.stderr,
                flush=True,
            )
            return (result.returncode if result.returncode > 0
                    else 128 - result.returncode)
        print(f"PASSED: {script.name}", flush=True)

    print("All three verifiers passed. Reports are in results/.", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
