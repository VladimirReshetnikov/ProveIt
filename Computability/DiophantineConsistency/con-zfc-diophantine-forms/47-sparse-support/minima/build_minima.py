#!/usr/bin/env python3
"""Generate two minimum-norm finalizers from the authenticated 61-gate source.

The original source is preserved byte for byte. Its old coefficient-binding
metadata is historical; emitted circuits use the complete, locally materialized
package-31 tuple through fixed_coefficients.json.
"""
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent
HISTORICAL_PIN = "5b0c9ae9fdae83db563f9d2b61ea0fb1f4a801e6"
COEFFICIENT_PIN = "124c07c0b77a9e20e84676514d8b1ff78536ea3f"
SOURCE_PATH = ("SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/"
               "con-zfc-diophantine-forms/12-gap-norm14/arithmetic/"
               "ordinary_gap_system61.json")

def build(coupled=False):
    old = json.loads((ROOT / "gap_system61.json").read_text())
    rows = [r[:] for r in old["source"]]
    if coupled:
        at = next(i for i, r in enumerate(rows) if r[0] == "transport_rhs")
        rows[at:at+1] = [
            ["transport_partial", "+", "innerC", "q_minus_F"],
            ["norm_transport", "-", "transport_partial", "local_rhs"]]
        rows += [["index_transport", "*", "norm_index", "norm_transport"],
                 ["unit_error", "-", "index_transport", 1]]
        residuals = ["norm_first", "norm_main", "norm_aux",
                     "unit_error", "strong_error"]
    else:
        rows += [["index_error", "-", "norm_index", 1],
                 ["transport_error", "-", "innerC", "transport_rhs"]]
        residuals = ["norm_first", "norm_main", "norm_aux",
                     "index_error", "transport_error", "strong_error"]
    rows += [["strong_error", "-", "ordinary_ic2_square", "R16"]]
    rows += [[r+"_sq", "*", r, r] for r in residuals]
    total = residuals[0]+"_sq"
    for j, r in enumerate(residuals[1:], 1):
        rows += [["total"+str(j), "+", total, r+"_sq"]]
        total = "total"+str(j)
    rows += [["polynomial", "-", total, 3]]
    expected = 75 if coupled else 76
    if len(rows) != expected:
        raise ValueError("incorrect gate count")
    return {
        "name": "gap_minima"+str(expected),
        "witnesses": old["witnesses"],
        "witness_domain": "strictly positive integers",
        "transport_coordinate": ("original z" if coupled else "shifted z_old-1"),
        "fixed_numerals": old["fixed_numerals"],
        "coefficient_binding": "fixed_coefficients.json",
        "coefficient_commit": COEFFICIENT_PIN,
        "source": rows, "output": "polynomial",
        "operations": len(rows), "ledger": dict(Counter(r[1] for r in rows)),
        "exact_degree": 44,
        "proof_scope": (
            "Integer minimum-norm equivalence to the ordinary gap system; "
            "the 75-gate version additionally imports signed index/transport "
            "recovery. Compiler and ZFC endpoint are inherited ordinary proofs."),
        "source_commit": HISTORICAL_PIN, "source_path": SOURCE_PATH,
        "source_git_blob_sha1": "2fa9af3e19a45c2429c62cd512b0b90551578d56",
    }

if __name__ == "__main__":
    for coupled in (False, True):
        d = build(coupled)
        (ROOT / (d["name"]+".json")).write_text(json.dumps(d, indent=2)+"\n")
        print(d["name"], d["operations"], d["ledger"])
