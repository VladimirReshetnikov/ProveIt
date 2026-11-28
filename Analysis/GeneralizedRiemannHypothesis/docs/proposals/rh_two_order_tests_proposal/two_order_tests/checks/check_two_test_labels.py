#!/usr/bin/env python3
"""Final two-test robust labels, retaining the original scalar modulus M.

Requires check_robust_labels.py in the same directory. The earlier conservative
M-full tests and their results remain separate. These are exact finite checks,
not a proof of the uniform theorem or a Lean verification.
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path

from check_robust_labels import factor, frobenius_degree, phi, run_case


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("two_test_labels_results.json"))
    args = parser.parse_args()
    cases = [(37, 3, 6, True), (73, 3, 6, True), (109, 3, 6, True),
             (37, 9, 6, False), (433, 3, 12, False), (1801, 3, 30, False),
             (1297, 3, 36, False)]
    results = []
    for q, r, m, exhaustive in cases:
        assert m % 6 == 0 and (q - 1) % (m * m) == 0
        row = run_case(q, r, m, exhaustive, selection_modulus=6)
        n, a = q**r - 1, q ** (r // 3)
        exact = (q**r - 3 * a + 2) // 3
        assert exact == row["expected_admissible_elements"]
        conservative = Fraction(phi(m), m) * (n - 3 * (a - 1))
        assert conservative.denominator == 1
        row["conservative_M_full_element_count"] = int(conservative)
        row["additional_elements_over_M_full"] = exact - int(conservative)
        row["ratio_over_M_full"] = str(Fraction(exact, conservative))
        if exhaustive:
            assert row["beyond_conservative_checked"] == row["additional_elements_over_M_full"]
        results.append(row)

    # Explicit distinction: 5 is excluded by the old M-full condition for M=30,
    # but it is accepted by the two fixed tests at 2 and 3.
    q, r, m, k = 1801, 3, 30, 5
    n, a = q**r - 1, q ** (r // 3)
    index = n // (3 * (a - 1))
    assert math.gcd(k, 6) == 1 and math.gcd(k, m) == 5 and k % index != 0
    norm_order = (q - 1) // math.gcd(k, q - 1)
    assert norm_order == 360 and norm_order % (m * m) != 0
    # The exact full 2,3-primary part of q-1 is still present.
    support_part = math.prod(p**e for p, e in factor(q - 1).items() if p in (2, 3))
    assert support_part == 72 and norm_order % support_part == 0
    strict_example = {
        "q": q, "r": r, "scalar_modulus_M": m, "selection_modulus": 6,
        "exponent": k, "gcd_with_6": 1, "gcd_with_M": 5,
        "norm_order": norm_order, "norm_full_2_3_primary_part": support_part,
        "M_squared_divides_norm_order": False,
        "explanation": "The fixed two-test condition is strictly weaker than M-full selection; it does not preserve the full prime-5 part of the norm.",
    }
    # This counterexample meets every final parameter assumption. A primitive
    # norm alone does not replace the deleted-subgroup condition.
    cq, cr, cm, ck = 37, 3, 6, 469
    cn = cq**cr - 1
    assert (cq - 1) % (cm * cm) == 0 and cm % 6 == 0
    assert math.gcd(ck, 6) == 1
    assert cn // math.gcd(ck, cn) == 108
    assert (cq - 1) // math.gcd(ck, cq - 1) == 36
    assert frobenius_degree(cq, cr, ck) == 3
    assert cn // math.gcd(3 * ck, cn) == 36
    assert frobenius_degree(cq, cr, 3 * ck) == 1
    norm_only_counterexample = {
        "q": cq, "r": cr, "scalar_modulus_M": cm, "exponent": ck,
        "group_order": cn, "H_order": 108, "H_index": 469,
        "passes_fixed_2_3_tests": True, "lies_in_H": True,
        "element_order": 108, "norm_order": 36, "norm_is_primitive": True,
        "degree_before": 3, "cubed_element_order": 36, "degree_after_cubing": 1,
        "explanation": "All final parameter assumptions hold, but deleting H is essential: z^3 lies in the ground field.",
    }
    accepted_examples = []
    for aq, ar, am, ak in [(37, 3, 6, 7), (1801, 3, 30, 25)]:
        an, aa = aq**ar - 1, aq**(ar // 3)
        assert math.gcd(ak, 6) == 1
        assert ak % (an // (3 * (aa - 1))) != 0
        assert frobenius_degree(aq, ar, ak) == ar
        ao = an // math.gcd(ak, an)
        assert ao < an
        for prime, power in factor(an).items():
            assert frobenius_degree(aq, ar, ak * prime**power) == ar
        accepted_examples.append({
            "q": aq, "r": ar, "scalar_modulus_M": am, "exponent": ak,
            "element_order": ao, "primitive_root": False,
            "norm_order": (aq - 1) // math.gcd(ak, aq - 1),
            "robust_under_every_primary_removal": True,
        })
    data = {
        "description": "Final fixed-two-test robust labels with unchanged scalar-order modulus",
        "scope": "Exact finite checks, not a uniform proof and not Lean kernel verification.",
        "hypotheses": "q prime power, r=3^a (a>=1), 6|M, M^2|q-1",
        "selection": "For z=g^k: gcd(k,6)=1 and z^3 not in F_(q^(r/3))^*",
        "element_count": "(q^r - 3*q^(r/3) + 2)/3",
        "polynomial_count": "(q^r - 3*q^(r/3) + 2)/(3*r)",
        "norm_guarantee": "The norm retains the entire 2-primary and 3-primary parts of q-1. Other primary parts are not claimed.",
        "source_specialization": "If 6^(s+6)|M then norm order is divisible by 6^(2*s+12).",
        "scalar_stability": "All c in F_q^* with c^M=1 preserve the selection.",
        "cases": results, "strict_enlargement_example": strict_example,
        "norm_only_counterexample_under_final_assumptions": norm_only_counterexample,
        "accepted_nonprimitive_examples": accepted_examples,
        "total_exponents_checked": sum(x["exponents_checked"] for x in results),
        "total_primary_removal_checks": sum(x["full_primary_removal_checks"] for x in results),
        "total_scalar_scaling_checks": sum(x["scalar_scaling_checks"] for x in results),
        "status": "all checks passed",
    }
    args.output.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({k: data[k] for k in ("status", "total_exponents_checked",
                                          "total_primary_removal_checks", "total_scalar_scaling_checks")}, indent=2))
    print("Results written to", args.output)


if __name__ == "__main__":
    main()
