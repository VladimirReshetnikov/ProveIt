"""Independent finite examples and rejection checks for certified_points."""
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import random

from certified_points import (
    Poly, Certificate, check_certificate, zero_witnesses,
    enumerate_rational_zeros, primitive_evaluation_witness,
    companion_certificate, certificate_as_json, certificate_from_json,
    mixed_radix_digits,
)

ROOT = Path(__file__).resolve().parents[1]


def elliptic_section():
    x, y = [Poly.variable(2, k) for k in range(2)]
    f = [4*y**2 - 4*x**3 + x - 4, 2*x**2 - x]
    b = [Poly.constant(2, 1), x, y, x*y]
    mx = [[0, 0, 0, 0], [1, Q(1, 2), 0, 0],
          [0, 0, 0, 0], [0, 0, 1, Q(1, 2)]]
    my = [[0, 0, 1, 0], [0, 0, 0, 1],
          [1, 0, 0, 0], [0, 1, 0, 0]]
    w = zero_witnesses(2, 4, 2)
    w[0][1][1] = Poly.constant(2, Q(1, 2))
    w[0][3][1] = y/2
    w[1][2] = [Poly.constant(2, Q(1, 4)), (2*x+1)/4]
    w[1][3] = [x/4, x*(2*x+1)/4]
    return Certificate(f, b, [1, 0, 0, 0], [Poly(2), Poly(2)], [mx, my], w)


def redundant_noncommuting():
    x, y = [Poly.variable(2, k) for k in range(2)]
    f = [x**2-x, 2*y-x]
    b = [Poly.constant(2, 1), x, x]
    mx = [[0, 0, 0], [1, 1, 1], [0, 0, 0]]
    my = [[0, 0, 0], [0, 0, 0], [Q(1, 2)]*3]
    w = zero_witnesses(2, 3, 2)
    w[0][1][0] = w[0][2][0] = Poly.constant(2, 1)
    w[1][0][1] = Poly.constant(2, Q(1, 2))
    w[1][1] = [Poly.constant(2, Q(1, 2)), x/2]
    w[1][2] = [Poly.constant(2, Q(1, 2)), x/2]
    return Certificate(f, b, [1, 0, 0], [Poly(2), Poly(2)], [mx, my], w)


def localization():
    x, y, t = [Poly.variable(3, k) for k in range(3)]
    f = [x*y, x*(x-1), t*x-1]
    w = zero_witnesses(3, 1, 3)
    w[0][0] = [Poly(3), t, -(x-1)]
    w[1][0] = [t, Poly(3), -y]
    w[2][0] = [Poly(3), -(t**2), 1+t*(x-1)]
    return Certificate(f, [Poly.constant(3, 1)], [1], [Poly(3)]*3,
                       [[[1]], [[0]], [[1]]], w)


def nondistinguished_unit():
    x = Poly.variable(1, 0)
    # The family (2, 3x) has no generator literally equal to 1.
    w = zero_witnesses(1, 2, 1)
    w[0][1][0] = Poly.constant(1, 3)
    return Certificate([x**2-x], [Poly.constant(1, 2), 3*x],
                       [Q(1, 2), 0], [Poly(1)],
                       [[[0, 0], [Q(2, 3), 1]]], w)


def linear_system(a, b):
    n = len(a)
    f = [a[k]*Poly.variable(n, k)-b[k] for k in range(n)]
    w = zero_witnesses(n, 1, n)
    for k in range(n):
        w[k][0][k] = Poly.constant(n, Q(1, a[k]))
    return Certificate(f, [Poly.constant(n, 1)], [1], [Poly(n)]*n,
                       [[[Q(b[k], a[k])]] for k in range(n)], w)


def matmul(a, b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(a)))
             for j in range(len(a))] for i in range(len(a))]


def check_case(name, cert, expected):
    assert check_certificate(cert) == (True, "accepted"), (name, check_certificate(cert))
    result = enumerate_rational_zeros(cert)
    points = result["points"]
    assert len(points) == len(set(points))
    assert set(points) == {tuple(map(Q, p)) for p in expected}, (name, points, expected)
    assert len(points) <= cert.dimension
    witnesses = [primitive_evaluation_witness(cert, p) for p in points]
    encoded = certificate_as_json(cert)
    decoded = certificate_from_json(encoded)
    assert enumerate_rational_zeros(decoded)["points"] == points
    return {
        "name": name, "certificate_dimension": cert.dimension,
        "candidates": result["candidates"], "bounds": result["bounds"],
        "points": [list(map(str, p)) for p in points], "witnesses": witnesses,
    }


def main():
    report = {"status": "passed", "arithmetic": "fractions.Fraction; integers only",
              "scope": "Finite implementation checks; not an iPRA proof checker",
              "cases": [], "counts": {}}
    cases = [
        ("elliptic_section", elliptic_section(), [(0, 1), (0, -1), (Q(1, 2), 1), (Q(1, 2), -1)]),
        ("noncommuting_redundant_generators", redundant_noncommuting(), [(0, 0), (1, Q(1, 2))]),
        ("localized_positive_dimensional_system", localization(), [(1, 0, 1)]),
        ("unit_is_a_linear_combination", nondistinguished_unit(), [(0,), (1,)]),
        ("nilpotent_quotient", companion_certificate([0, 0, 1]), [(0,)]),
        ("no_rational_roots", companion_certificate([-2, 0, 1]), []),
        ("two_rational_denominators", companion_certificate([Q(1, 6), Q(-5, 6), 1]), [(Q(1, 3),), (Q(1, 2),)]),
        ("zero_radius", companion_certificate([0, 1]), [(0,)]),
    ]
    out = ROOT / "examples"
    out.mkdir(exist_ok=True)
    for name, cert, expected in cases:
        report["cases"].append(check_case(name, cert, expected))
        (out / f"{name}.json").write_text(json.dumps(certificate_as_json(cert), indent=2)+"\n")
    redundant = cases[1][1]
    a, b = redundant.actions
    assert matmul(a, b) != matmul(b, a), "Test must really use noncommuting matrices"

    # Independently known solutions of many exact rational linear systems.
    rng = random.Random(20261115)
    for _ in range(90):
        n = rng.randrange(1, 4)
        a = [rng.randrange(1, 8) for _ in range(n)]
        b = [rng.randrange(-3, 4) for _ in range(n)]
        cert = linear_system(a, b)
        expected = [tuple(Q(v, u) for u, v in zip(a, b))]
        check_case("linear_system", cert, expected)
    report["counts"]["independent_linear_systems"] = 90

    # Supplied roots give an independent factor-product oracle, including repeats.
    root_sets = [[Q(a, b) for a, b in roots] for roots in [
        [(0, 1)], [(1, 2), (1, 2)], [(-2, 3), (1, 2)],
        [(-1, 1), (0, 1), (1, 1)], [(1, 3), (-1, 3), (2, 3)],
    ]]
    for roots in root_sets:
        coefficients = [Q(1)]
        for r in roots:
            new = [Q(0)]*(len(coefficients)+1)
            for i, c in enumerate(coefficients):
                new[i] -= r*c
                new[i+1] += c
            coefficients = new
        check_case("factored_polynomial", companion_certificate(coefficients), [(r,) for r in set(roots)])
    report["counts"]["independent_factored_polynomials"] = len(root_sets)

    # Reject changes which would otherwise justify a false grid or no valid unit.
    rejected = []
    bad = deepcopy(elliptic_section()); bad.actions[0][1][1] = Q(2, 3)
    rejected.append(bad)
    bad = deepcopy(elliptic_section()); bad.unit = [0]*4
    rejected.append(bad)
    bad = deepcopy(elliptic_section()); bad.witnesses[1][2][0] = Poly(2)
    rejected.append(bad)
    bad = deepcopy(elliptic_section()); bad.actions[0] = [[0]]
    rejected.append(bad)
    bad = deepcopy(elliptic_section()); bad.unit_witness = []
    rejected.append(bad)
    report["rejection_reasons"] = []
    for bad in rejected:
        ok, why = check_certificate(bad)
        assert not ok
        report["rejection_reasons"].append(why)
        try:
            enumerate_rational_zeros(bad)
        except ValueError:
            pass
        else:
            raise AssertionError("Enumeration accepted an invalid certificate")
    report["counts"]["invalid_certificates_rejected"] = len(rejected)

    grids = 0
    for radices in product(range(1, 5), repeat=3):
        size = radices[0]*radices[1]*radices[2]
        decoded = {tuple(mixed_radix_digits(i, radices)) for i in range(size)}
        expected = set(product(*(range(b) for b in radices)))
        assert decoded == expected
        grids += 1
    report["counts"]["independent_grid_bijections"] = grids
    report["counts"]["featured_cases"] = len(cases)
    destination = ROOT/"validation"/"point_enumeration_checks.json"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"status": "passed", "counts": report["counts"]}, indent=2))


if __name__ == "__main__":
    main()
