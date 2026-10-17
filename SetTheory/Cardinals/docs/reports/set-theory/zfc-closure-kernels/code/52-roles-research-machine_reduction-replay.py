#!/usr/bin/env python3
"""Replay the frozen register-role experiment using only Python's standard library."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("repo", type=Path, help="ProveIt checkout/materialization at beb2c633ae57a0883d28fb6d0c75342d08cfdeda")
parser.add_argument("--recompute-masks", action="store_true", help="Recompute the finite mask invariant first; its elapsed-time field will change")
args = parser.parse_args()
repo = args.repo.resolve()
expected = json.loads((ROOT / "frozen/SHA256SUMS.json").read_text())

stages = []
if args.recompute_masks:
    stages.append(("value_analysis.py", ["32"]))
stages.extend([
    ("freeze_allocation.py", []),
    ("allocation_certificate.py", []),
    ("allocated_dag.py", []),
    ("compact_allocated_dag.py", []),
    ("compile_controls.py", [str(repo)]),
])
for name, extra in stages:
    print("RUN", name, flush=True)
    subprocess.run([sys.executable, str(ROOT / name), *extra], cwd=ROOT, check=True)

checks = []
for name in ["static-coalescing.json", "allocation-certificate.json", "allocated-dag.json", "allocated-dag-compacted.json"]:
    digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    assert digest == expected["frozen/" + name], (name, "frozen output mismatch")
    checks.append(name)
for name in ["frozen/original_control.tm", "frozen/coalesced_control.tm", "frozen/complete-table-controls.json"]:
    digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    assert digest == expected[name], (name, "frozen output mismatch")
    checks.append(name)
print(json.dumps({"status": "PASS exact replay", "checked_outputs": checks}, indent=2))
