#!/usr/bin/env python3
"""Replay all finite checks; never enumerate the giant window list."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
CHECKS = [
    ("fixed-input circuits", ["artifacts/fixed_input.py", "--output",
                              "artifacts/fixed_input.json"]),
    ("explicit domain conversions", ["artifacts/domain_variants.py", "--output",
                                     "artifacts/domain_variants.json"]),
    ("explicit normalizer", ["artifacts/compiler/k215_one_sided.py"]),
    ("finite census and layout", ["artifacts/compiler/finite_window_constants.py"]),
    ("independent circuit and controller review",
     ["artifacts/review/review_fixed70.py"]),
]


def main():
    logs = ROOT / "artifacts/verification"
    logs.mkdir(exist_ok=True)
    results = []
    for number, (name, arguments) in enumerate(CHECKS, 1):
        result = subprocess.run(
            [sys.executable, *arguments], cwd=ROOT, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        log = logs / f"check_{number}.txt"
        log.write_text(result.stdout)
        results.append({
            "name": name, "arguments": ["python3", *arguments],
            "returncode": result.returncode,
            "output": log.relative_to(ROOT).as_posix(),
            "output_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
        })
        print(f"{name}: {'PASS' if result.returncode == 0 else 'FAIL'}", flush=True)
        if result.returncode:
            print(result.stdout[-6000:])
            break
    passed = len(results) == len(CHECKS) and all(
        row["returncode"] == 0 for row in results
    )
    receipt = {
        "status": "PASS" if passed else "FAIL",
        "checks": results,
        "scope": (
            "Finite arithmetic, circuit, local-controller and compressed-census "
            "checks. No proof-assistant build, giant coefficient expansion, "
            "complete window enumeration, or consistency decision."
        ),
    }
    (logs / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    raise SystemExit(0 if passed else 1)


if __name__ == "__main__":
    main()
