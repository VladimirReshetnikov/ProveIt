#!/usr/bin/env python3
"""Reproduce the new exact diagnostics without altering historical records."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import subprocess
import sys


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, default=Path("audit_rerun"))
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    scripts = Path(__file__).resolve().parent
    jobs = [
        ("hypercube_verify.py", "hypercube_validation.json", True),
        ("plane_checks.py", "plane_validation.json", False),
        ("triangle_checks.py", "triangle_validation.json", True),
        ("box_bm.py", "box_bm_validation.json", True),
    ]
    for name, result_name, accepts_output in jobs:
        target = out/result_name
        cmd = [sys.executable, str(scripts/name)]
        if accepts_output:
            cmd += ["--output", str(target)]
        result = subprocess.run(cmd, check=True, capture_output=True, text=True)
        if not accepts_output:
            json.loads(result.stdout)
            target.write_text(result.stdout)
        json.loads(target.read_text())
        print(f"Passed: {name} -> {target.name}")
    print("All finite diagnostics passed; these are not internal iPRA proofs.")


if __name__ == "__main__":
    main()

