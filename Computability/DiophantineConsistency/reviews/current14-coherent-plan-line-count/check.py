#!/usr/bin/env python3
"""Count the hashed sources selected by the stopped current14 rebuild."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
PLAN = ROOT / "Computability/DiophantineConsistency/research/current14-coherent-extension-refactor-retry05-runner/plan.json"
plan_bytes = PLAN.read_bytes()
assert hashlib.sha256(plan_bytes).hexdigest() == "b0006cd71994ebafccbd65a30d41e11cb8d953f52751b2c98f3884df3e63744c"
plan = json.loads(plan_bytes)
entries = plan["entries"]
assert len(entries) == 529
sources = {entry["source"] for entry in entries}
assert len(sources) == len(entries)
lines = 0
for entry in entries:
    data = (ROOT / entry["source"]).read_bytes()
    assert hashlib.sha256(data).hexdigest() == entry["source_sha256"], entry["module"]
    lines += len(data.splitlines())
assert lines == 57208, lines
print(f"Verified {len(sources)} pinned sources; {lines:,} physical lines.")
print("The base modules, Lean execution, and endpoint proof are outside this count.")
