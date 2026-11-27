#!/usr/bin/env python3
"""Cross-check two formula implementations against saved exhaustive enumeration.

This does not re-enumerate frame tuples. It recomputes the exact probability
of every saved Gram matrix using exact_law.py, whose embedding and kernel
counts use different formulas from exhaustive_check.py.
"""

from fractions import Fraction
import hashlib
import json
from pathlib import Path

import exact_law
import exhaustive_check


def main():
    packet = Path(__file__).resolve().parents[1]
    source = packet / "results" / "exhaustive_checks.json"
    data = json.loads(source.read_text())
    checked = 0
    for case in data["cases"]:
        q, n = case["q"], case["ambient_half_dimension"]
        dims = tuple(case["block_dimensions"])
        half_ranks = tuple(x // 2 for x in case["individual_gram_ranks"])
        denominator = case["frame_tuples_enumerated"]
        for item in case["pointwise_counts"]:
            gamma = exhaustive_check.block_gram(
                item["cross_gram_entries"], dims, q, half_ranks)
            result = exact_law.matrix_probability(q, n, dims, gamma)
            expected = Fraction(item["observed_count"], denominator)
            assert Fraction(result["probability"]) == expected
            assert result["total_half_rank"] * 2 == item["rank"]
            assert result["radical_intersections"] == item["block_radical_intersections"]
            checked += 1
        moment = exact_law.nullity_moment(q, dims, half_ranks)
        assert moment == Fraction(case["uniform_mean_q_to_nullity"]["exact"])
        bounds = exact_law.tv_bounds(q, n, dims, half_ranks)
        actual_tv = Fraction(case["exact_total_variation"]["exact"])
        assert Fraction(bounds["tv_lower"]) <= actual_tv <= Fraction(bounds["tv_upper"])
    assert checked == data["total_gram_matrices_checked"]
    files = ["code/exact_law.py", "code/exhaustive_check.py", "results/exhaustive_checks.json"]
    summary = {
        "verification_status": "all exact checks passed",
        "scope": "Finite exact verification, not a formal proof of the general theorems",
        "number_of_exhaustive_cases": data["number_of_cases"],
        "actual_frame_tuples_previously_enumerated": data["total_frame_tuples_enumerated"],
        "gram_matrices_checked_pointwise": data["total_gram_matrices_checked"],
        "independent_implementation_crosschecks": checked,
        "nonisotropic_cases": sum(any(c["individual_gram_ranks"]) for c in data["cases"]),
        "forest_marginals_checked": sum(c["forest_marginals_checked"] for c in data["cases"]),
        "exact_support_criterion_checked": all(c["exact_support_criterion_checked"] for c in data["cases"]),
        "radical_moment_formula_checked": True,
        "total_variation_bounds_checked": all(c["theorem_tv_bound_checked"] for c in data["cases"]),
        "prime_fields_checked": sorted({c["q"] for c in data["cases"]}),
        "independence_of_implementations": {
            "exhaustive_check": "Actual frame enumeration; direct multi-index Moebius sum; rational eta-product embedding formula",
            "exact_law": "No frame enumeration; q-binomial polynomial recurrence; symplectic-group order times radical-frame product",
            "rank_checks": "Independent finite-field elimination implementations"
        },
        "formalization_status": "Written proof and finite exact tests; not formalized in Lean; no Lean executable available",
        "source_sha256": {name: hashlib.sha256((packet / name).read_bytes()).hexdigest() for name in files},
        "reproduce": ["python3 code/exhaustive_check.py", "python3 code/cross_check_implementations.py"]
    }
    output = packet / "results" / "verification_summary.json"
    output.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
