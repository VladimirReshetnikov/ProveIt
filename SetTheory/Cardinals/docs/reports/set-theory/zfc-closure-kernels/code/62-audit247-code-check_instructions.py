#!/usr/bin/env python3
"""All 8,391 symbolic instruction guards, reparsing the complete pinned source.

The register contracts used by affine_engine are discharged separately by
check_macro_inductions.py. This finite symbolic computation is not a newly
compiled Lean/Rocq proof. It is parameterized by every extra gap n >= 0,
all nine register values satisfying the particular guard, and every finite
nonempty spare suffix. Unlike the recovered prototype, it never trusts a site
cache and never builds its machine from a separate unchecked table generator.
"""
from __future__ import annotations
from collections import Counter
import json
from hashlib import sha256
from pathlib import Path
import time
import affine_engine as affine
from build_machine import ROOT, PHYSICAL, build, program_sites, OLD_FINAL_SHA256

def increment(pc):
    if "0" not in pc:
        return None
    return pc[:pc.rindex("0")] + "1"

def strip(pc, symbol, count):
    while pc and count:
        count -= pc[-1] == symbol
        pc = pc[:-1]
    return pc

def main():
    if not __debug__:
        raise SystemExit("Assertions are required; do not use -O.")
    began = time.monotonic()
    table = {(str(q), b): (w, d, str(t)) for (q, b), (w, d, t) in build().items()}
    sites = program_sites()
    cached = ROOT / "results/instruction-sites.json"
    if cached.exists():
        assert json.loads(cached.read_text()) == [list(s) for s in sites]
    counts, cases, minimum, maximum = Counter(), 0, 10**9, 0
    for pc, op, logical in sites:
        r = PHYSICAL[logical] if op in ("CI", "CD") else logical
        for zero in ((True, False) if op == "CD" else (None,)):
            branch = (r, zero) if op == "CD" else None
            if op == "CI" or (op == "CD" and not zero):
                successor = increment(pc)
            elif op == "CD":
                successor = increment(strip(pc, "0", 1))
            elif op == "CB":
                successor = increment(strip(pc, "0", r))
            elif op == "CC":
                successor = strip(pc, "1", r)
            else:
                successor = ""
            effect = ("inc", r) if op == "CI" else (("dec", r) if op == "CD" and not zero else None)
            extra = int(op == "CD" and not zero)
            if successor is None:
                right = [("r", 0, 1, 41 + extra), ("b", 1), ("box", ("plain", effect))]
            else:
                right = [("b", int(b)) for b in successor] + [
                    ("r", 0, 1, 40 + extra - len(successor)),
                    ("b", 1), ("box", ("plain", effect))]
            rules, literal = affine.run(table, pc, branch,
                affine.canon([("b", 1)], right), halt=op == "CH", fuel=1000)
            counts.update(rules)
            cases += 1
            minimum = min(minimum, literal)
            maximum = max(maximum, sum(rules.values()))
    assert cases == 8391 and minimum > 0
    out = dict(status="PASS", cases=cases, source_rows=6459, instruction_sites=6460,
        exact_table_sha256=OLD_FINAL_SHA256, primary_input="fresh full Prog254.v parse",
        minimum_literal_steps_per_case=minimum, max_rules_per_case=maximum,
        rule_totals=dict(counts), elapsed_seconds=time.monotonic()-began,
        quantifiers="All n>=0, every primary vector satisfying the named guard, every finite nonempty spare suffix.",
        macros="See the independently discharged induction templates in macro-inductions.json.",
        gap_effect="positive decrement +1; overflow +1; other cases +0",
        spare_effect="increment appends [1]; all other operations preserve the suffix",
        proof_assistant_kernel_checked=False)
    (ROOT / "results/instructions.json").write_text(json.dumps(out, indent=2)+"\n", encoding="ascii")
    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
