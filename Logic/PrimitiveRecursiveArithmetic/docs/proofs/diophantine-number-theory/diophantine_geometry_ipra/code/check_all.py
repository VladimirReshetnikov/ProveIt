#!/usr/bin/env python3
"""Reproducible exact checks; their finite scope is not a mathematical proof."""
import json
from fractions import Fraction
from itertools import product
from math import gcd, isqrt
from pathlib import Path

import conics
import descent
import geometry as g


def geometry_checks():
    counts = {}
    norm_checks = 0
    for v in product(range(-4, 5), repeat=3):
        if not any(v):
            continue
        normalized = g.canonical(v)
        assert g.gcd_all(normalized) == 1
        assert next(x for x in normalized if x) > 0
        for scale in (-3, -1, 1, 2, 4):
            assert g.canonical(tuple(scale * x for x in v)) == normalized
            norm_checks += 1
    counts["normalization_and_scaling_cases"] = norm_checks

    circle_checks = 0
    for p in g.projective_points(1, 15):
        point = g.circle_parameter(*p)
        assert point[0] ** 2 + point[1] ** 2 == point[2] ** 2
        assert g.circle_inverse(point) == p
        circle_checks += 1
    counts["circle_inverse_cases"] = circle_checks

    pairs, nondegenerate, inequalities = 0, 0, 0
    forms = list(product((-1, 0, 1), repeat=3))
    points = g.projective_points(1, 4)
    for f, h in product(forms, repeat=2):
        pairs += 1
        r = g.determinant(g.sylvester(f, h))
        if r == 0:
            try:
                g.map_certificate(f, h)
                raise AssertionError("degenerate pair accepted")
            except ValueError:
                pass
            continue
        cert = g.map_certificate(f, h)
        nondegenerate += 1
        assert 1 <= cert["lower_constant"] <= cert["coarse_lower_constant"]
        for p in points:
            raw = (g.form_eval(f, *p), g.form_eval(h, *p))
            content = g.gcd_all(raw)
            assert content > 0 and r % content == 0
            image = g.rational_map(f, h, p)
            assert g.height(p) ** 2 <= cert["lower_constant"] * g.height(image)
            assert g.height(image) <= cert["upper_constant"] * g.height(p) ** 2
            inequalities += 1
    counts["quadratic_coefficient_pairs"] = pairs
    counts["nonzero_resultants"] = nondegenerate
    counts["exact_height_comparisons"] = inequalities

    expected = {(0, 1), (1, -1), (1, 0), (1, 1)}
    for f in ((1, 0, 0), (1, 0, -1)):
        cert, found = g.preperiodic_points(f, (0, 0, 1))
        assert {p["point"] for p in found} == expected
        for witness in found:
            orbit = [witness["point"]]
            for _ in range(witness["j"]):
                orbit.append(g.rational_map(f, (0, 0, 1), orbit[-1]))
            assert 0 <= witness["i"] < witness["j"]
            assert orbit[witness["i"]] == orbit[witness["j"]]
    counts["complete_dynamical_examples"] = 2

    elliptic_cases = 0
    for a, b in product(range(-2, 3), repeat=2):
        bound = 8
        independent = set()
        for numerator, denominator in g.projective_points(1, bound):
            if denominator == 0:
                continue
            x = Fraction(numerator, denominator)
            rhs = x ** 3 + a * x + b
            if rhs >= 0:
                rn, rd = isqrt(rhs.numerator), isqrt(rhs.denominator)
                if rn * rn == rhs.numerator and rd * rd == rhs.denominator:
                    independent.add((x, Fraction(rn, rd)))
                    independent.add((x, Fraction(-rn, rd)))
        assert set(g.elliptic_points_xheight(a, b, bound)) == independent
        elliptic_cases += 1
    counts["elliptic_complete_list_comparisons"] = elliptic_cases

    assert g.rational_roots([0, 6, -5, 1]) == [Fraction(0), Fraction(2), Fraction(3)]
    assert g.rational_roots([-1, 0, 4]) == [Fraction(-1, 2), Fraction(1, 2)]
    assert g.rational_roots([1, 0, 1]) == []
    assert g.rational_roots([1]) == []
    counts["rational_root_examples"] = 4

    obstruction = [(1, (2, 0, 0)), (1, (0, 2, 0)), (-3, (0, 0, 2))]
    assert len(g.residue_solutions(2, 3, [obstruction])) == 2
    assert g.residue_solutions(2, 9, [obstruction]) == []
    counts["modular_obstruction_checks"] = 2

    assert g.projective_points(2, 0) == []
    try:
        g.canonical((0, 0))
        raise AssertionError("zero vector accepted")
    except ValueError:
        pass
    try:
        g.eval_polynomial([(1, (1,))], (2, 3))
        raise AssertionError("malformed exponent tuple accepted")
    except ValueError:
        pass
    counts["boundary_and_invalid_input_cases"] = 3
    return counts


def main():
    results = {"status": "all exact arithmetic checks passed",
               "scope": "finite executable verification, separate from the written proofs",
               "geometry": geometry_checks(),
               "conics": conics.validate(),
               "descent": descent.check_examples()}
    root = Path(__file__).resolve().parents[1]
    (root / "evidence" / "validation.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
