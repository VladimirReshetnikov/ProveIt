#!/usr/bin/env python3
"""Confirm that the attractive 194-state quotient is REJECTED by its runtime."""
from pathlib import Path
import json
import sys
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "reference_pa195_packet/pa195"))
import build_verify as v
c = v.c
def main():
    v.need(__debug__ and not sys.flags.optimize, "Run without Python -O")
    prefix = ROOT / "evidence/rejected_candidate_194/near194_bad4_k17595"
    tree = c.read_grammar(prefix.with_suffix(".json"))
    raw, _, shape = c.build(tree)
    folds = json.loads(prefix.with_suffix(".folds.json").read_text())
    folded, aliases = v.quotient(raw, folds)
    v.need(len(raw) == 404 and len(folded) == 388, "Raw/folded state count")
    v.need(folded == v.table(prefix.with_suffix(".native.tm")), "Rejected table reconstruction")
    certificate = v.quotient_certificate(raw, folded, folds, aliases)
    v.need(certificate["local_cases"] == 32, "Expected eight local folds")
    sites, cfg, contracts = c.source(tree)
    source = v.source_binding(tree, sites, cfg)
    emitter = v.emitter(tree)
    failed = c.validate(raw, contracts)
    v.need(failed == {"ok": False, "failed": (1003, (2, True)), "completed": 1309},
           "The recorded negative runtime control no longer agrees")
    result = {
        "check_passed": True,
        "candidate_status": "REJECTED: not a validated Con(PA) machine",
        "working_states": len(folded) // 2,
        "compatible_folds": len(folds),
        "source_binding": source,
        "emitter": emitter,
        "expected_runtime_failure": failed,
        "scope": "A successful local quotient does not repair the invalid source encoding."
    }
    print(json.dumps(result, indent=2))
if __name__ == "__main__":
    main()
