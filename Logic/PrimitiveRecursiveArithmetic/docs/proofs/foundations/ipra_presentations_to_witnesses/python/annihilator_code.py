"""Construct exact finite-module certificates from separated annihilators.

The input for variable k is a monic positive-degree coefficient list q_k,
in increasing degree order, and explicit polynomials h[k][ell] witnessing
    q_k(X_k) = sum_ell h[k][ell] * equations[ell].
Every identity is checked before construction.  No ideal-membership search,
factorization, Groebner algorithm, or certificate oracle is used.

The proof is in the accompanying paper.  This executable reference is not an
iPRA proof checker.  It uses exactly the same rational sparse-polynomial and
row-vector matrix convention as certified_points.py.
"""

from fractions import Fraction as Q
from itertools import product
from math import prod

from certified_points import (
    Poly, Certificate, zero_witnesses, linear_combination,
    check_certificate, enumerate_rational_zeros, mixed_radix_digits,
    primitive_evaluation_witness,
)


def separated_annihilator_certificate(equations, coefficients, ideal_witnesses):
    """Build a certificate from checked monic separated ideal identities.

    ``coefficients[k][i]`` is the coefficient of T**i in q_k.  The final
    coefficient must be 1, and each list must have at least two entries.
    ``ideal_witnesses[k][ell]`` multiplies equations[ell] in the identity
    for q_k(X_k).  All input polynomials have n=len(coefficients) variables.

    Box monomials are ordered with coordinate zero as the least significant
    mixed-radix digit; for degrees (2,2) the basis is (1,x,y,xy).
    """
    equations = list(equations)
    coefficients = [list(map(Q, cs)) for cs in coefficients]
    n = len(coefficients)
    if n < 1:
        raise ValueError("At least one coordinate annihilator is required")
    if any(len(cs) < 2 or cs[-1] != 1 for cs in coefficients):
        raise ValueError("Each annihilator must be monic of positive degree")
    if any(not isinstance(f, Poly) or f.n != n for f in equations):
        raise ValueError("Equation polynomial arity mismatch")
    witnesses = [list(row) for row in ideal_witnesses]
    s = len(equations)
    if len(witnesses) != n or any(len(row) != s for row in witnesses):
        raise ValueError("Ideal-witness dimensions mismatch")
    if any(not isinstance(h, Poly) or h.n != n
           for row in witnesses for h in row):
        raise ValueError("Ideal-witness polynomial arity mismatch")

    for k, cs in enumerate(coefficients):
        x = Poly.variable(n, k)
        q = sum((c * x**i for i, c in enumerate(cs)), Poly(n))
        if q != linear_combination(witnesses[k], equations, n):
            raise ValueError(f"Separated ideal identity failed at coordinate {k}")

    degrees = [len(cs) - 1 for cs in coefficients]
    dimension = prod(degrees)
    exponents = [tuple(mixed_radix_digits(j, degrees))
                 for j in range(dimension)]
    basis = [Poly(n, {e: Q(1)}) for e in exponents]
    actions = [[[Q(0) for _ in range(dimension)]
                for _ in range(dimension)] for _ in range(n)]
    residual_witnesses = zero_witnesses(n, dimension, s)

    stride = 1
    for k, dk in enumerate(degrees):
        for j, e in enumerate(exponents):
            if e[k] + 1 < dk:
                actions[k][j + stride][j] = Q(1)
            else:
                for i in range(dk):
                    row = j + (i - e[k]) * stride
                    actions[k][row][j] = -coefficients[k][i]
                without_k = list(e)
                without_k[k] = 0
                multiplier = Poly(n, {tuple(without_k): Q(1)})
                residual_witnesses[k][j] = [
                    multiplier * h for h in witnesses[k]
                ]
        stride *= dk

    cert = Certificate(
        equations, basis, [Q(1)] + [Q(0)] * (dimension - 1),
        [Poly(n) for _ in range(s)], actions, residual_witnesses,
    )
    accepted, reason = check_certificate(cert)
    if not accepted:
        raise AssertionError("Constructed certificate failed verification: " + reason)
    return cert


def coefficients_from_roots(roots):
    """Independent finite factor-product oracle used only by diagnostics."""
    out = [Q(1)]
    for root in map(Q, roots):
        nxt = [Q(0)] * (len(out) + 1)
        for i, value in enumerate(out):
            nxt[i] -= root * value
            nxt[i + 1] += value
        out = nxt
    return out


def separated_system_from_roots(root_lists):
    """Independent-variable equations with identity membership witnesses."""
    n = len(root_lists)
    coefficients = [coefficients_from_roots(rs) for rs in root_lists]
    equations = []
    for k, cs in enumerate(coefficients):
        x = Poly.variable(n, k)
        equations.append(sum((c*x**i for i, c in enumerate(cs)), Poly(n)))
    witnesses = [[Poly.constant(n, int(k == ell)) for ell in range(n)]
                 for k in range(n)]
    return equations, coefficients, witnesses


def _check_case(name, data, expected):
    cert = separated_annihilator_certificate(*data)
    assert check_certificate(cert) == (True, "accepted")
    result = enumerate_rational_zeros(cert)
    points = result["points"]
    expected = {tuple(map(Q, p)) for p in expected}
    assert set(points) == expected, (name, points, expected)
    assert len(points) == len(set(points))
    assert len(points) <= cert.dimension
    evaluation_witnesses = [primitive_evaluation_witness(cert, p) for p in points]
    return {
        "name": name,
        "degrees": [len(cs) - 1 for cs in data[1]],
        "certificate_dimension": cert.dimension,
        "candidate_count": result["candidates"],
        "bounds": result["bounds"],
        "points": [list(map(str, p)) for p in points],
        "evaluation_witnesses": evaluation_witnesses,
    }


def run_diagnostics():
    report = {
        "status": "passed",
        "scope": "Exact finite constructor checks, not an iPRA proof checker",
        "arithmetic": "fractions.Fraction and integers",
        "cases": [],
        "rejections": [],
    }

    root_families = [
        ("tensor_product_rational_roots", [[Q(-1, 2), Q(2, 3)], [0, -2]]),
        ("mixed_degrees_three_variables", [[Q(1, 2)], [-1, 1], [0]]),
        ("all_degree_one", [[Q(3, 5)], [-2], [0]]),
        ("degree_one_zero_constant", [[0]]),
        ("repeated_root", [[Q(1, 2), Q(1, 2), -1]]),
    ]
    for name, roots in root_families:
        report["cases"].append(_check_case(
            name, separated_system_from_roots(roots), product(*roots)))

    x, y = [Poly.variable(2, k) for k in range(2)]
    elliptic = (
        [4*y**2 - 4*x**3 + x - 4, 2*x**2 - x],
        [[0, Q(-1, 2), 1], [-1, 0, 1]],
        [[Poly(2), Poly.constant(2, Q(1, 2))],
         [Poly.constant(2, Q(1, 4)), (2*x+1)/4]],
    )
    report["cases"].append(_check_case(
        "elliptic_section_from_ideal_identities", elliptic,
        [(0, -1), (0, 1), (Q(1, 2), -1), (Q(1, 2), 1)]))
    assert report["cases"][-1]["candidate_count"] == 15

    no_roots = (
        [x**2 + 1, y**2 - 2], [[1, 0, 1], [-2, 0, 1]],
        [[Poly.constant(2, 1), Poly(2)],
         [Poly(2), Poly.constant(2, 1)]],
    )
    report["cases"].append(_check_case("empty_rational_product", no_roots, []))

    base = separated_system_from_roots([[Q(1, 2)]])
    invalid = [
        ("invalid_membership_identity", (base[0], base[1], [[Poly(1)]])),
        ("degree_zero_annihilator", (base[0], [[1]], base[2])),
        ("nonmonic_annihilator", (base[0], [[-1, 2]], base[2])),
        ("missing_membership_witness", (base[0], base[1], [[]])),
        ("wrong_polynomial_arity", ([Poly.variable(2, 0)], base[1], base[2])),
    ]
    for name, data in invalid:
        try:
            separated_annihilator_certificate(*data)
        except ValueError as error:
            report["rejections"].append({"name": name, "reason": str(error)})
        else:
            raise AssertionError("Invalid separated data accepted: " + name)
    report["counts"] = {
        "valid_constructors": len(report["cases"]),
        "invalid_inputs_rejected": len(report["rejections"]),
        "constructed_action_identities": sum(
            len(case["degrees"])*case["certificate_dimension"]
            for case in report["cases"]),
    }
    return report


if __name__ == "__main__":
    import argparse
    import json
    from pathlib import Path

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path,
                        default=Path(__file__).resolve().parents[1] /
                        "validation" / "annihilator_constructor_checks.json")
    args = parser.parse_args()
    report = run_diagnostics()
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "counts": report["counts"]}, indent=2))
