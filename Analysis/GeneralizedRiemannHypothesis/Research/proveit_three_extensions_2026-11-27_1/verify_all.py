#!/usr/bin/env python3
"""Run the four independently executable mathematical verification programs."""
from pathlib import Path
import importlib.metadata
import json
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
PROGRAMS = [
    Path("papers/gram_determinants/verify_gram.py"),
    Path("papers/positive_filters/check_mirror.py"),
    Path("papers/bilinear_detection/verify.py"),
    Path("verification/independent_counts.py"),
]

def main():
    if not __debug__:
        raise SystemExit("Run without -O: these checkers use assertions.")
    rows = []
    all_passed = True
    for relative in PROGRAMS:
        start = time.monotonic()
        print(f"Checking {relative}", flush=True)
        result = subprocess.run(
            [sys.executable, str(ROOT / relative)],
            cwd=(ROOT / relative).parent, capture_output=True, text=True,
        )
        logfile = ROOT / "verification" / (relative.stem + ".run.txt")
        logfile.write_text(result.stdout + result.stderr)
        rows.append({
            "program": str(relative), "exit_code": result.returncode,
            "elapsed_seconds": round(time.monotonic() - start, 3),
            "log": str(logfile.relative_to(ROOT)),
        })
        print(f"  {'PASS' if result.returncode == 0 else 'FAIL'}", flush=True)
        all_passed = all_passed and result.returncode == 0
    packages = {name: importlib.metadata.version(name)
                for name in ["numpy", "sympy", "mpmath", "matplotlib"]}
    report = {
        "all_passed": all_passed,
        "python": platform.python_version(),
        "packages": packages,
        "programs": rows,
        "scope": "Finite and symbolic verification supports the written proofs; "
                 "it is not a proof assistant certificate.",
    }
    (ROOT / "verification/run_summary.json").write_text(
        json.dumps(report, indent=2) + "\n")
    if not all_passed:
        raise SystemExit(1)

if __name__ == "__main__":
    main()
