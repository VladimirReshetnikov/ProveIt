#!/usr/bin/env python3
"""Run the five independent mathematical verification programs.

The universal theorems are proved in the manuscript. These programs
check exact identities and finite examples, with numerical checks
identified separately in each output. No network access is required.
"""
from pathlib import Path
import importlib.metadata
import json
import platform
import subprocess
import sys
import time


def main():
    project = Path(__file__).resolve().parents[1]
    scripts = [
        "verify_quotient.py",
        "verify_twelfth_order.py",
        "verify_odd_cube_expansion.py",
        "verify_odd_rigidity.py",
        "verify_six_ap_defect.py",
    ]
    outcomes = []
    for name in scripts:
        started = time.monotonic()
        result = subprocess.run(
            [sys.executable, str(project / "code" / name)],
            cwd=project,
            capture_output=True,
            text=True,
        )
        elapsed = time.monotonic() - started
        outcomes.append({
            "script": name,
            "exit_code": result.returncode,
            "seconds": round(elapsed, 3),
        })
        (project / "data" / (Path(name).stem + "_run.txt")).write_text(
            result.stdout + result.stderr
        )
        print(f"{name}: {'PASS' if result.returncode == 0 else 'FAIL'} "
              f"({elapsed:.2f} s)", flush=True)
        if result.returncode:
            print(result.stdout + result.stderr, file=sys.stderr)
    report = {
        "status": "passed" if all(x["exit_code"] == 0 for x in outcomes) else "failed",
        "scope": "Exact algebraic certificates and explicitly labeled finite numerical checks; no proof-assistant certification.",
        "python": platform.python_version(),
        "packages": {x: importlib.metadata.version(x)
                     for x in ("numpy", "sympy", "mpmath", "matplotlib")},
        "checks": outcomes,
    }
    (project / "data" / "verification_run.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    return int(report["status"] != "passed")


if __name__ == "__main__":
    raise SystemExit(main())
