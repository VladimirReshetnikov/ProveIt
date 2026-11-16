"""Complete rational intersections from a nonzero monic-plane norm.

Standard library only. Uses the sparse exact Poly datatype in certified_points.
This is a reference implementation of finite algorithms, not an iPRA checker.
The accompanying paper proves the universal mathematical claims. The tests
exercise exact finite cases, including rejected and empty intersections.
"""
from fractions import Fraction as Q
from itertools import permutations
from math import gcd, prod

from certified_points import (Poly, Certificate, check_certificate,
                              enumerate_rational_zeros)


def univariate_coefficients(p):
    if p.n != 1:
        raise ValueError("Expected a univariate polynomial")
    if not p.terms:
        return []
    degree = max(e[0] for e in p.terms)
    return [p.terms.get((i,), Q(0)) for i in range(degree + 1)]


def root_bound(p):
    """Return the rational-root bound, rejecting an identically zero input."""
    coefficients = univariate_coefficients(p)
    if not coefficients:
        raise ValueError("The zero polynomial has no supported finite root list")
    delta = prod(c.denominator for c in coefficients)
    integer_coefficients = [int(delta * c) for c in coefficients]
    first = next(c for c in integer_coefficients if c)
    last = integer_coefficients[-1]
    return max(1, abs(first), abs(last))


def rational_roots(p):
    """Bounded exhaustive scan of canonical rational pairs."""
    bound = root_bound(p)
    roots = []
    tested = 0
    for numerator in range(-bound, bound + 1):
        for denominator in range(1, bound + 1):
            if gcd(abs(numerator), denominator) != 1:
                continue
            tested += 1
            value = Q(numerator, denominator)
            if p.evaluate((value,)) == 0:
                roots.append(value)
    return {"roots": roots, "bound": bound, "canonical_candidates": tested,
            "pair_bound": (2 * bound + 1) * bound}


def y_coefficients(p):
    if p.n != 2:
        raise ValueError("Expected a polynomial in X and Y")
    if not p.terms:
        return []
    degree = max(e[1] for e in p.terms)
    coefficients = [Poly(1) for _ in range(degree + 1)]
    for (x_degree, y_degree), c in p.terms.items():
        coefficients[y_degree] += Poly(1, {(x_degree,): c})
    return coefficients


def monic_y_data(f):
    coefficients = y_coefficients(f)
    if len(coefficients) < 2 or coefficients[-1] != 1:
        raise ValueError("F must have positive Y-degree and leading coefficient one")
    return coefficients


def lift_x(p):
    if p.n != 1:
        raise ValueError("Expected a univariate coefficient polynomial")
    return Poly(2, {(e[0], 0): c for e, c in p.terms.items()})


def divide_y(p, monic_coefficients):
    """Finite monic division; retain quotient and m remainder coefficients."""
    m = len(monic_coefficients) - 1
    if m < 1 or monic_coefficients[-1] != 1:
        raise ValueError("Invalid monic divisor")
    coefficients = y_coefficients(p)
    coefficients += [Poly(1) for _ in range(max(0, m - len(coefficients)))]
    quotient = Poly(2)
    y = Poly.variable(2, 1)
    for degree in range(len(coefficients) - 1, m - 1, -1):
        top = coefficients[degree]
        quotient += lift_x(top) * y ** (degree - m)
        for i in range(m):
            coefficients[degree - m + i] -= top * monic_coefficients[i]
        coefficients[degree] = Poly(1)
    return quotient, coefficients[:m]


def reduce_y(p, monic_coefficients):
    return divide_y(p, monic_coefficients)[1]


def divide_univariate_monic(p, q):
    coefficients = univariate_coefficients(q)
    if len(coefficients) < 2 or coefficients[-1] != 1:
        raise ValueError("Positive-degree monic univariate divisor required")
    d = len(coefficients) - 1
    remainder = p
    quotient = Poly(1)
    original_degree = max((e[0] for e in p.terms), default=-1)
    for k in range(original_degree, d - 1, -1):
        c = remainder.terms.get((k,), Q(0))
        term = Poly(1, {(k - d,): c})
        quotient += term
        remainder -= term * q
    return quotient, remainder


def determinant(matrix):
    """Leibniz determinant over Q[X], with no elimination oracle."""
    n = len(matrix)
    if n < 1 or any(len(row) != n for row in matrix):
        raise ValueError("A positive square matrix is required")
    result = Poly(1)
    for perm in permutations(range(n)):
        inversions = sum(perm[i] > perm[j] for i in range(n)
                         for j in range(i + 1, n))
        term = Poly.constant(1, -1 if inversions % 2 else 1)
        for i in range(n):
            term *= matrix[i][perm[i]]
        result += term
    return result


def norm_data(f, g):
    coefficients = monic_y_data(f)
    if g.n != 2:
        raise ValueError("G must have two variables")
    m = len(coefficients) - 1
    y = Poly.variable(2, 1)
    columns = [reduce_y(g * y ** j, coefficients) for j in range(m)]
    matrix = [[columns[j][i] for j in range(m)] for i in range(m)]
    return {"norm": determinant(matrix), "matrix": matrix,
            "monic_coefficients": coefficients}


def adjugate(matrix):
    n = len(matrix)
    if n < 1 or any(len(row) != n for row in matrix):
        raise ValueError("Positive square polynomial matrix required")
    result = [[Poly(1) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            # Entry (i,j) is cofactor (j,i).
            minor = [[matrix[r][c] for c in range(n) if c != i]
                     for r in range(n) if r != j]
            value = determinant(minor) if minor else Poly.constant(1, 1)
            result[i][j] = value if (i + j) % 2 == 0 else -value
    return result


def norm_certificate(f, g):
    """Produce a unit/action certificate or a checked inconsistency identity.

    This implements the adjugate membership identity N = U G + V F,
    then monic reductions in the rectangle X^i Y^j, i<deg N, j<deg_Y F.
    Its output is fed to the independently defined certificate checker.
    """
    data = norm_data(f, g)
    norm = data["norm"]
    if not norm.terms:
        raise ValueError("Identically zero norm: this certificate is unsupported")
    x, y = Poly.variable(2, 0), Poly.variable(2, 1)
    m = len(data["monic_coefficients"]) - 1
    adj = adjugate(data["matrix"])
    quotients = [divide_y(g * y ** j, data["monic_coefficients"])[0]
                 for j in range(m)]
    u = sum((y ** j * lift_x(adj[j][0]) for j in range(m)), Poly(2))
    v = -sum((quotients[j] * lift_x(adj[j][0]) for j in range(m)), Poly(2))
    if lift_x(norm) != u * g + v * f:
        raise AssertionError("Norm ideal-membership identity failed")
    norm_coefficients = univariate_coefficients(norm)
    d = len(norm_coefficients) - 1
    leading = norm_coefficients[-1]
    if d == 0:
        return {"kind": "inconsistent", "equations": [f, g],
                "witnesses": [v / leading, u / leading], "norm": norm}
    q = norm / leading
    q_coefficients = univariate_coefficients(q)
    q_witnesses = [v / leading, u / leading]
    exponents = [(i, j) for j in range(m) for i in range(d)]
    indices = {e: index for index, e in enumerate(exponents)}
    size = len(exponents)
    basis = [x ** i * y ** j for i, j in exponents]
    actions = [[[Q(0) for _ in range(size)] for _ in range(size)]
               for _ in range(2)]
    witnesses = [[[Poly(2), Poly(2)] for _ in range(size)] for _ in range(2)]
    tx = Poly.variable(1, 0)
    for column, (i, j) in enumerate(exponents):
        if i < d - 1:
            actions[0][indices[(i + 1, j)]][column] = Q(1)
        else:
            for k in range(d):
                actions[0][indices[(k, j)]][column] = -q_coefficients[k]
            witnesses[0][column] = [y ** j * w for w in q_witnesses]
        if j < m - 1:
            actions[1][indices[(i, j + 1)]][column] = Q(1)
        else:
            witnesses[1][column] = [x ** i, Poly(2)]
            for k in range(m):
                a = -(tx ** i) * data["monic_coefficients"][k]
                quotient, remainder = divide_univariate_monic(a, q)
                for (power,), coefficient in remainder.terms.items():
                    actions[1][indices[(power, k)]][column] += coefficient
                multiplier = lift_x(quotient) * y ** k
                for equation in range(2):
                    witnesses[1][column][equation] += multiplier * q_witnesses[equation]
    cert = Certificate(equations=[f, g], generators=basis,
                       unit=[Q(1)] + [Q(0)] * (size - 1),
                       unit_witness=[Poly(2), Poly(2)],
                       actions=actions, witnesses=witnesses)
    return {"kind": "finite_module", "certificate": cert, "norm": norm,
            "norm_membership": [v, u], "dimension": size}


def rational_intersections(f, g):
    """Return every rational common zero when the polynomial norm is nonzero."""
    data = norm_data(f, g)
    norm = data["norm"]
    if not norm.terms:
        raise ValueError("Identically zero norm: this certificate is unsupported")
    x_scan = rational_roots(norm)
    points = []
    fibers = []
    height = max(1, x_scan["bound"])
    for x in x_scan["roots"]:
        coefficients = [p.evaluate((x,)) for p in data["monic_coefficients"]]
        fiber = Poly(1, {(j,): c for j, c in enumerate(coefficients)})
        y_scan = rational_roots(fiber)
        height = max(height, y_scan["bound"])
        fibers.append({"x": x, "scan": y_scan})
        for y in y_scan["roots"]:
            if g.evaluate((x, y)) == 0:
                points.append((x, y))
    return {"points": points, "height_bound": height,
            "norm": norm, "x_scan": x_scan, "fibers": fibers,
            "matrix": data["matrix"]}


def scalar_determinant(matrix):
    """Independent exact Gaussian determinant for diagnostic comparisons."""
    matrix = [list(map(Q, row)) for row in matrix]
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("Square scalar matrix required")
    result = Q(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if matrix[i][j]), None)
        if pivot is None:
            return Q(0)
        if pivot != j:
            matrix[j], matrix[pivot] = matrix[pivot], matrix[j]
            result = -result
        p = matrix[j][j]
        result *= p
        for i in range(j + 1, n):
            ratio = matrix[i][j] / p
            for k in range(j + 1, n):
                matrix[i][k] -= ratio * matrix[j][k]
            matrix[i][j] = Q(0)
    return result


def verify_cases():
    x, y = Poly.variable(2, 0), Poly.variable(2, 1)
    t = Poly.variable(1, 0)
    cases = [
        ("repeated_first_coordinate_fibers", y ** 2 - x ** 3 + x - 1,
         x ** 2 - x, (t ** 2 - t) ** 2,
         [(0, -1), (0, 1), (1, -1), (1, 1)]),
        ("degree_one_monic_fiber", y - x / 2 - Q(1, 3),
         3 * x - 1, 3 * t - 1, [(Q(1, 3), Q(1, 2))]),
        ("nonzero_constant_norm", y ** 2 - x, Poly.constant(2, 1),
         Poly.constant(1, 1), []),
        ("extraneous_norm_root_irrational_fiber", y ** 2 - 2, x,
         t ** 2, []),
        ("extraneous_norm_root_nonreal_fiber", y ** 2 + 1, x,
         t ** 2, []),
        ("singular_repeated_root", y ** 2 - x ** 2, x,
         t ** 2, [(0, 0)]),
        ("separate_denominators_23_and_29", y - Q(7, 29),
         x - Q(1, 23), t - Q(1, 23), [(Q(1, 23), Q(7, 29))]),
        ("higher_Y_degree_reduction", y ** 2 - x, y ** 3 - y,
         -t * (t - 1) ** 2, [(0, 0), (1, -1), (1, 1)]),
        ("cubic_fiber", y ** 3 - x, y - 2,
         t - 8, [(8, 2)]),
        ("negative_first_coordinate", y ** 2 - x - 1, x + 1,
         (t + 1) ** 2, [(-1, 0)]),
        ("final_section_filter", y ** 2 - 1, y - x,
         t ** 2 - 1, [(-1, -1), (1, 1)]),
    ]
    records = []
    determinant_checks = 0
    reductions_checked = 0
    module_checks = 0
    grid_comparisons = 0
    inconsistency_checks = 0
    for name, f, g, expected_norm, expected_points in cases:
        result = rational_intersections(f, g)
        assert result["norm"] == expected_norm, name
        expected = {tuple(map(Q, p)) for p in expected_points}
        assert set(result["points"]) == expected, name
        assert len(result["points"]) == len(set(result["points"])), name
        for point in result["points"]:
            assert f.evaluate(point) == 0 and g.evaluate(point) == 0, name
            assert all(max(abs(q.numerator), q.denominator) <= result["height_bound"]
                       for q in point), name
        # Independent scalar elimination checks the actual norm determinant.
        for value in [-2, 0, 3]:
            evaluated = [[p.evaluate((value,)) for p in row]
                         for row in result["matrix"]]
            assert scalar_determinant(evaluated) == result["norm"].evaluate((value,)), name
            determinant_checks += 1
        # For each actual rational common zero, check the evaluation row.
        m = len(result["matrix"])
        for a, b in result["points"]:
            row = [b ** i for i in range(m)]
            for j in range(m):
                assert sum(row[i] * result["matrix"][i][j].evaluate((a,))
                           for i in range(m)) == g.evaluate((a, b)) * row[j], name
                reductions_checked += 1
        constructed = norm_certificate(f, g)
        if constructed["kind"] == "inconsistent":
            wf, wg = constructed["witnesses"]
            assert wf * f + wg * g == 1, name
            assert not expected, name
            inconsistency_checks += 1
            certificate_evidence = {"kind": "inconsistent", "identity_checked": True}
        else:
            accepted, reason = check_certificate(constructed["certificate"])
            assert accepted, name + ": " + reason
            module_checks += 1
            grid_result = enumerate_rational_zeros(constructed["certificate"])
            assert set(grid_result["points"]) == set(result["points"]), name
            grid_comparisons += 1
            certificate_evidence = {"kind": "finite_module",
                                    "dimension": constructed["dimension"],
                                    "grid_candidates": grid_result["candidates"],
                                    "identity_checks": "accepted",
                                    "two_enumerators_agree": True}
        records.append({"case": name, "norm": result["norm"].as_json(),
                        "points": [[str(a), str(b)] for a, b in result["points"]],
                        "height_bound": result["height_bound"],
                        "x_pair_bound": result["x_scan"]["pair_bound"],
                        "fiber_pair_bounds": [v["scan"]["pair_bound"]
                                               for v in result["fibers"]],
                        "norm_to_module": certificate_evidence})
    failures = [
        ("G_identically_zero", y ** 2 - x, Poly(2)),
        ("G_multiple_of_F", y ** 2 - x, y ** 2 - x),
        ("nonmonic_F", 2 * y ** 2 - x, x),
        ("degree_zero_F", Poly.constant(2, 1), x),
    ]
    rejected = []
    for name, f, g in failures:
        try:
            rational_intersections(f, g)
        except ValueError as exc:
            rejected.append({"case": name, "reason": str(exc)})
        else:
            raise AssertionError(name + " was not rejected")
    # Direct root tests distinguish zero, nonzero constants, and monomials.
    root_tests = [
        (Poly.constant(1, 7), []),
        (3 * t ** 5, [Q(0)]),
        ((2 * t - 1) * (3 * t + 2), [Q(-2, 3), Q(1, 2)]),
    ]
    for p, roots in root_tests:
        assert set(rational_roots(p)["roots"]) == set(roots)
    try:
        rational_roots(Poly(1))
    except ValueError:
        pass
    else:
        raise AssertionError("Zero polynomial root scan was not rejected")
    return {"status": "passed", "arithmetic": "exact fractions.Fraction",
            "scope": "finite implementation checks, not universal proofs or an iPRA checker",
            "counts": {"intersection_cases": len(cases),
                       "independent_determinant_evaluations": determinant_checks,
                       "evaluation_row_identities": reductions_checked,
                       "constructed_module_certificates_checked": module_checks,
                       "independent_grid_enumeration_comparisons": grid_comparisons,
                       "constant_norm_inconsistency_identities": inconsistency_checks,
                       "unsupported_intersections_rejected": len(rejected),
                       "direct_rational_root_cases": len(root_tests),
                       "zero_polynomial_rejected": 1},
            "cases": records, "rejected": rejected}


if __name__ == "__main__":
    import json
    import sys
    from pathlib import Path
    report = verify_cases()
    text = json.dumps(report, indent=2) + "\n"
    if len(sys.argv) > 1:
        Path(sys.argv[1]).write_text(text)
    print(text)
