#!/usr/bin/env python3
"""Check agreement of all profiles, not only the maximum or histogram."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
a = json.loads((ROOT / "data/lattice_certificates.json").read_text())
b = json.loads((ROOT / "data/independent_dvr_results.json").read_text())
A = {tuple(c["residue_multiplicities"]): c for c in
     a["eight_term_open_global"]["profile_certificates"]}
B = {tuple(c["residue_multiplicities"]): c for c in b["certificates"]}
assert len(A) == len(B) == 165 and A.keys() == B.keys()
for profile in A:
    x, y = A[profile], B[profile]
    assert x["support"] == y["support"]
    assert x["maximum"] == y["maximum"]
    assert x["rank_increase_indices"] == y["pivot_indices"]
    assert x["hnf_determinant_valuation"] == sum(y["smith_valuations"])
assert a["eight_term_open_global"]["distribution"] == b["distribution"]
print(json.dumps({"profiles_compared":165, "all_maxima_agree":True,
                  "all_prefix_ranks_agree":True, "all_lattice_indices_agree":True,
                  "distribution":b["distribution"]}, indent=2))

