#!/usr/bin/env python3
"""Replay only the four standalone Init-only checks in this packet."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--lean", default="lean", help="Path to Lean 4.32.0")
parser.add_argument("--logs", type=Path, default=ROOT / "validation")
args = parser.parse_args()
args.logs.mkdir(parents=True, exist_ok=True)
version = subprocess.run([args.lean, "--version"], capture_output=True, text=True, check=True).stdout.strip()
if not re.search(r"version 4\.32\.0(?:,|\s)", version):
    raise SystemExit("Expected repository-pinned Lean 4.32.0; received " + version)
results = []
for source in sorted((ROOT / "lean" / "checked").glob("*.lean")):
    start = time.perf_counter()
    run = subprocess.run([args.lean, str(source)], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    duration = time.perf_counter() - start
    (args.logs / (source.stem + ".log")).write_text(run.stdout)
    result = {
        "file": str(source.relative_to(ROOT)),
        "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "returncode": run.returncode,
        "elapsed_seconds": round(duration, 6),
        "contains_sorryAx": "sorryAx" in run.stdout,
        "axiom_reports": [line for line in run.stdout.splitlines()
                          if "axioms" in line or "any axioms" in line],
    }
    results.append(result)
    print(source.name, "PASS" if run.returncode == 0 and not result["contains_sorryAx"] else "FAIL")
receipt = {
    "compiler": version,
    "scope": "Standalone Init-only kernels; no Mathlib adapter, production module, or dependency build.",
    "production_integration_compiled": False,
    "results": results,
}
(args.logs / "core-results.json").write_text(json.dumps(receipt, indent=2) + "\n")
sys.exit(0 if all(r["returncode"] == 0 and not r["contains_sorryAx"] for r in results) else 1)
