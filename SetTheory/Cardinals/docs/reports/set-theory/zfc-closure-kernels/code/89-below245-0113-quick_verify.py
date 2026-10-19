#!/usr/bin/env python3
"""Replay the exact certificate and selected abstract grammar witnesses."""
import json
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parent
# Flags must remain literal, whereas data paths are relative to this file.
def replay(script, *args):
    values = [x if x.startswith("--") else str(root/x) for x in args]
    result = subprocess.run([sys.executable, str(root/script), *values],
                            check=True, capture_output=True, text=True)
    return json.loads(result.stdout)

proof = replay("verify_restricted_bound.py", "lp128_restricted.lp.json.gz",
               "restricted_bound128_certificate.json.gz", "--inputs",
               "restricted_universe_inputs.json")
audits = []
for name in ("baseline_seed20261018.json", "coupled20261018.json", "mip128_len40.json"):
    result = replay("audit_search_grammar.py", name,
                    "--route-grammar", "reference/inputs/state_reduction/route-grammar.txt",
                    "--constraints", "reference/inputs/state_reduction/route-constraints.txt",
                    "--bootstrap", "reference/inputs/state_reduction/bootstrap-lock54.txt")
    audits.append(dict(file=name, **result))
for family in ("permutation_seeds", "anchored_seeds"):
    for i in range(3):
        p = f"{family}/{i}/"
        result = replay("audit_search_grammar.py", p+"result.json",
                        "--route-grammar", p+"route-grammar.txt",
                        "--constraints", p+"route-constraints.txt",
                        "--bootstrap", p+"bootstrap-lock54.txt",
                        "--source-seed", p+"seed.json",
                        "--semantic-rows", "reference/research/architecture/semantic_rows.json",
                        "--parts", "axiom_parts_original.json")
        audits.append(dict(file=p+"result.json", **result))
print(json.dumps(dict(status="PASS", certificate=proof,
                      abstract_grammar_audits=audits,
                      binary_machine_checks_performed=False), indent=2))
