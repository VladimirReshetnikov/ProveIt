#!/usr/bin/env python3
"""Independent diagnostics for the fixed-prefix full-complex lower bound.

The proof is mathematical.  This script checks the concrete diagram conventions,
the recurrence, exact crossing counts, and small scalar homology values.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
FAST = ROOT
sys.path.insert(0, str(FAST))
sys.path.insert(0, str(FAST / "tests"))

from fastunknot import Diagram, recognize
from fastunknot.alexander import alexander_polynomial, evaluate
from test_fastunknot import reference_reduced_rank


def cf_column(coefficients):
    """Forward continued-fraction matrices, independently of production code."""
    a, b, c, d = 1, 0, 0, 1
    for value in coefficients:
        a, b, c, d = a * value + b, a, c * value + d, c
    return a, c


def main():
    rows = []
    p, q, r, s = 1, 1, 3, 2
    last_p = None
    for k in range(21):
        left = [1] if k == 0 else [2] * (2 * k - 1) + [3]
        right_positive = [2] * (2 * k) + [1, 2]
        right = [-a for a in right_positive]
        assert cf_column(left) == (p, q)
        assert cf_column(right_positive) == (r, s)
        assert p * s - q * r == -1
        assert p % 2 == q % 2 == 1
        assert sum(map(abs, left)) == 4 * k + 1
        assert sum(map(abs, right)) == 4 * k + 3

        whole = Diagram.from_rational(0, [left, right])
        assert whole.crossings == 8 * k + 4
        result = recognize(whole)
        assert result.status == "UNKNOT"
        row = {
            "k": k,
            "prefix_crossings": 4 * k + 1,
            "whole_crossings": whole.crossings,
            "p": p,
            "q": q,
            "r": r,
            "s": s,
            "full_complex_summand_lower_bound": (p + 1) // 2,
            "graded_full_complex_summand_lower_bound": p + q,
            "actual_closure_status": result.status,
        }
        if k <= 6:
            prefix_closure = Diagram.from_rational(0, [left])
            det = abs(evaluate(alexander_polynomial(prefix_closure), -1))
            assert det == p
            row["independent_alexander_determinant"] = det
            inverse_closure = Diagram.from_rational(0, [[0] + left])
            inverse_det = abs(evaluate(alexander_polynomial(inverse_closure), -1))
            assert inverse_det == q
            row["independent_denominator_determinant"] = inverse_det
            if k <= 2:
                rank = reference_reduced_rank(prefix_closure)
                assert rank >= p
                row["independent_cube_reduced_rank"] = rank
                inverse_rank = reference_reduced_rank(inverse_closure)
                assert inverse_rank >= q
                row["independent_denominator_cube_reduced_rank"] = inverse_rank
        rows.append(row)
        new_p, new_q = 5 * p + 2 * q, 2 * p + q
        if last_p is not None:
            assert new_p == 6 * p - last_p
        last_p, p, q = p, new_p, new_q
        r, s = 5 * r + 2 * s, 2 * r + s

    output = {
        "all_checks_passed": True,
        "diagram_instances": len(rows),
        "independent_Alexander_checks": 14,
        "independent_cube_rank_checks": 6,
        "scope": "Diagnostics support the stated conventions; proof supplies the asymptotic lower bound.",
        "instances": rows,
    }
    path = Path(sys.argv[1])
    path.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({key: value for key, value in output.items() if key != "instances"}, indent=2))


if __name__ == "__main__":
    main()
