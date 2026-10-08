#!/usr/bin/env python3
"""Run the integrated suite and independent mathematical checks, without benchmarks."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
FAST = ROOT / "implementation" / "fast"
VERIFY = ROOT / "verification"


def main():
    environment = os.environ.copy()
    environment["PYTHONPATH"] = str(FAST)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    jobs = [
        ("full_suite", FAST, ["-m", "unittest", "discover", "-s", "tests", "-v"]),
        ("graded_transfer", ROOT, [str(VERIFY / "graded_transfer" / "validate_transfer.py")]),
        ("tail_referee", ROOT, [str(VERIFY / "referee_tail.py")]),
        ("repair_dag", ROOT, [str(VERIFY / "repair_dag_bound.py")]),
    ]
    records = []
    for name, cwd, arguments in jobs:
        start = time.perf_counter()
        result = subprocess.run([sys.executable, *arguments], cwd=cwd, env=environment,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output = VERIFY / (name + ".txt")
        output.write_text(result.stdout)
        record = {"name": name, "exit_code": result.returncode,
                  "seconds": time.perf_counter() - start,
                  "log": str(output.relative_to(ROOT))}
        if name == "full_suite":
            match = re.search(r"Ran (\d+) tests in ([0-9.]+)s", result.stdout)
            if match:
                record["test_count"] = int(match.group(1))
                record["unittest_seconds"] = float(match.group(2))
        records.append(record)
        print(f"{name}: {'PASS' if result.returncode == 0 else 'FAIL'} "
              f"({record['seconds']:.3f}s)", flush=True)
        if result.returncode:
            print(result.stdout[-6000:], flush=True)
            break
    modules = ["graded_transfer.py", "symbolic_braid.py", "twist/long_tail.py"]
    report = {"status": "PASS" if len(records) == len(jobs) and
              all(r["exit_code"] == 0 for r in records) else "FAIL",
              "python": platform.python_version(), "platform": platform.platform(),
              "jobs": records,
              "module_sha256": {
                  name: hashlib.sha256((FAST / "fastunknot" / name).read_bytes()).hexdigest()
                  for name in modules}}
    (VERIFY / "integrated_validation.json").write_text(json.dumps(report, indent=2) + "\n")
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
