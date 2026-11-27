#!/usr/bin/env python3
"""Compare formula-based laws with independent complete matrix enumeration.

Run independent_enumeration.py first, or use the supplied exact JSON.
All comparisons use fractions.Fraction, including zeros.
"""
from fractions import Fraction as F
from pathlib import Path
import json

from exact_laws import laws
from joint_laws import joint_law


def main():
    out = Path(__file__).resolve().parents[1] / "results"
    cases = json.loads((out / "independent_enumeration.json").read_text())["cases"]
    marginal_equalities = joint_equalities = 0
    for case in cases:
        q, a, b = (case[k] for k in ("q", "a", "b"))
        exact = laws(q, a, b)
        comparisons = (
            ("rank", "symp_nullity_weights", "symplectic_frame_total"),
            ("rank_iid", "iid_nullity_counts", "iid_total"),
            ("defect", "iid_defect_nullity_counts", "iid_total"),
            ("defect_symplectic", "symp_defect_nullity_weights", "symplectic_frame_total"),
        )
        for formula_key, count_key, total_key in comparisons:
            for k in range(b + 1):
                enumerated = F(case[count_key].get(str(k), 0), case[total_key])
                assert exact[formula_key][k] == enumerated, (q, a, b, formula_key, k)
                marginal_equalities += 1
        for formula_key, count_key in (
            ("full_tv", "full_matrix_tv"),
            ("rank_tv", "rank_tv"),
            ("defect_tv", "defect_vs_alt_tv"),
        ):
            assert exact[formula_key] == F(case[count_key]["exact"]), (q, a, b, formula_key)
            marginal_equalities += 1

        joint = joint_law(q, a, b)
        for k in range(b + 1):
            for ell in range(b + 1):
                enumerated = F(
                    case["iid_joint_nullity_counts"].get(f"{k},{ell}", 0),
                    case["iid_total"],
                )
                assert joint["joint"][k][ell] == enumerated, (q, a, b, k, ell)
                joint_equalities += 1
        assert joint["dependence_tv"] == F(case["iid_joint_vs_product_tv"]["exact"])
        joint_equalities += 1

    marginal = dict(status="PASS", equalities=marginal_equalities, cases=len(cases),
                    method="embedding moments versus direct matrix enumeration")
    joint_result = dict(status="PASS", equalities=joint_equalities, cases=len(cases),
                        method="mixed moments versus direct matrix enumeration")
    (out / "independent_comparison.json").write_text(json.dumps(marginal, indent=2) + "\n")
    (out / "joint_independent_comparison.json").write_text(json.dumps(joint_result, indent=2) + "\n")
    print(json.dumps(marginal))
    print(json.dumps(joint_result))


if __name__ == "__main__":
    main()

