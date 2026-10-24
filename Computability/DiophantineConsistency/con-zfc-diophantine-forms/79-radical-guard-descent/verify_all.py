#!/usr/bin/env python3
"""Offline release verification. Python 3.10+, standard library only."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
JOBS = [
    ("integer", "build.py"),
    ("integer/audit", "check_independent.py"),
    ("positive11", "rebuild_coefficients.py"),
    ("positive11", "verify.py"),
    ("nine_positive", "rebuild_coefficients.py"),
    ("nine_positive", "verify.py"),
    ("alternative", "single_loop.py"),
    ("alternative", "build_local_adapter.py"),
]


def main():
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["PYTHONOPTIMIZE"] = str(sys.flags.optimize)
    records = []
    for directory, script in JOBS:
        path = ROOT / directory / script
        print("Checking " + directory + "/" + script, flush=True)
        process = subprocess.run([sys.executable, str(path)], cwd=path.parent,
                                 env=env, capture_output=True, text=True)
        if process.returncode:
            print(process.stdout, end="")
            print(process.stderr, end="", file=sys.stderr)
            raise RuntimeError("Verification failed: " + directory + "/" + script)
        records.append({"script": directory + "/" + script,
                        "status": "PASS",
                        "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    result = {
        "status": "PASS", "python_optimization": sys.flags.optimize,
        "source_commit": "2605669a532342f153b13eb6b4a0af4b54f5fa37",
        "checks": records,
        "scope": "Exact finite algebra, circuit reconstruction, coefficient regeneration and source-adapter diagnostics. The ordinary unbounded semantic proof dependencies are stated in report.tex; this is not a formal ZFC certificate."
    }
    suffix = "_OPTIMIZED" if sys.flags.optimize else ""
    (ROOT / ("VERIFICATION" + suffix + ".json")).write_text(
        json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
