#!/usr/bin/env python3
"""Run the packet's exact, finite diagnostics and retain their output.

These programs are not an iPRA proof checker or the Lean kernel.  Polynomial
normalization is universal for the identities it checks; the solid checks
exhaust the five specified finite examples; the observation checks exercise
the stated finite ranges.  The human proofs address the general statements.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
TASKS = [
    ("polynomial_certificates", ["code/check_certificates.py", "--output", "certificates/polynomials.json"]),
    ("circle_identities", ["code/check_circle_identities.py"]),
    ("platonic_realizations", ["code/check_solids.py", "--output", "certificates/solids.json"]),
    ("measurement_observations", ["code/check_limits.py"]),
]


def main() -> None:
    destination = ROOT / "verification"
    destination.mkdir(exist_ok=True)
    results = []
    for name, arguments in TASKS:
        command = [sys.executable, *arguments]
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        output = result.stdout + result.stderr
        (destination / f"{name}.log").write_text(output, encoding="utf-8")
        results.append({
            "name": name,
            "command": ["python3", *arguments],
            "exit_code": result.returncode,
            "passed": result.returncode == 0,
            "log": f"verification/{name}.log",
            "source_sha256": hashlib.sha256((ROOT / arguments[0]).read_bytes()).hexdigest(),
        })
        print(f"{name}: {'PASS' if result.returncode == 0 else 'FAIL'}", flush=True)
        print(output.rstrip(), flush=True)
    status = {
        "python_version": platform.python_version(),
        "all_diagnostics_passed": all(r["passed"] for r in results),
        "checks": results,
        "lean_compiled": False,
        "ipra_kernel_checked": False,
        "scope_note": "Exact executable diagnostics, distinct from the report's human proofs and the uncompiled Lean candidates.",
    }
    (destination / "status.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    if not status["all_diagnostics_passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
