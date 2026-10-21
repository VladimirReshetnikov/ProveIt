#!/usr/bin/env python3
"""Check complete word/CFG equality for the selected saved source finalists."""
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE / "vendor"))
import source_language as s
import source_splice as sp

assert __debug__, "Assertions must be enabled"
raw = (ROOT / "reference/primary215/sites215.json").read_bytes()
assert hashlib.sha256(raw).hexdigest() == "17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba"
baseline = json.loads(raw)
word = [row[1:] for row in baseline]
graph = sp.cfg_intervals(baseline)
assert graph == sp.cfg_arithmetic(baseline)
count = 0
for folder in sorted((HERE / "runs").iterdir()):
    receipt = json.loads((folder / "summary.json").read_text())
    records = {x["source"]: x for x in receipt["finalists"]}
    for name in receipt["shipped_sources"]:
        raw = (folder / name).read_bytes()
        rec = records[name]
        assert hashlib.sha256(raw).hexdigest() == rec["sha256"]
        rows = json.loads(raw)
        assert [row[1:] for row in rows] == word
        assert sp.cfg_intervals(rows) == sp.cfg_arithmetic(rows) == graph
        assert s.metrics(s.tree(rows)) == rec["metrics"]
        count += 1
print(json.dumps({"status": "SAVED_SOURCE_FULL_WORD_AND_DUAL_CFG_PASS", "sources": count,
                  "scope": "Exact supplied sources only; no physical allocation or optimality claim."}, indent=2))
