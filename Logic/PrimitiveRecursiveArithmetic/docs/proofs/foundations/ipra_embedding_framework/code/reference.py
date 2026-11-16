"""Exact reference algorithms for the accompanying mathematical report.

Only Python's standard library is required. These computations check examples
and finite certificates; they are not a proof of universal iPRA derivability.
All mathematically significant comparisons use integers or Fraction.
"""
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path


def common_window(sequences, tolerances, variation_bounds, exceptions,
                  exception_budgets, width, start=0):
    """Check the finite hypotheses, then return a successful common window."""
    if len(sequences) != len(tolerances) or len(sequences) != len(variation_bounds):
        raise ValueError("sequence data lengths differ")
    if len(exceptions) != len(exception_budgets):
        raise ValueError("exception data lengths differ")
    if any(e <= 0 for e in tolerances) or any(v < 0 for v in variation_bounds):
        raise ValueError("invalid rational budget")
    if any(c < 0 for c in exception_budgets):
        raise ValueError("negative count budget")
    budget = sum(int(v // e) for v, e in zip(variation_bounds, tolerances))
    budget += sum(exception_budgets)
    endpoints = [start]
    for _ in range(budget + 1):
        n = endpoints[-1]
        w = width(n)
        if w < 0:
            raise ValueError("negative window width")
        endpoints.append(n + w + 1)
    final = endpoints[-1]
    variations = [sum((abs(a(t + 1) - a(t)) for t in range(final)), Q(0))
                  for a in sequences]
    counts = [sum(bool(e(t)) for t in range(final)) for e in exceptions]
    if any(v > bound for v, bound in zip(variations, variation_bounds)):
        raise ValueError("finite variation hypothesis failed")
    if any(c > bound for c, bound in zip(counts, exception_budgets)):
        raise ValueError("finite exception hypothesis failed")
    for i, n in enumerate(endpoints[:-1]):
        end = n + width(n)
        oscillations = []
        for a in sequences:
            values = [a(t) for t in range(n, end + 1)]
            oscillations.append(max(values) - min(values))
        if (all(o <= e for o, e in zip(oscillations, tolerances))
                and all(not any(e(t) for t in range(n, end + 1)) for e in exceptions)):
            return {
                "budget": budget, "selected_index": i, "start": n, "end": end,
                "start_bound": endpoints[-2], "finite_demand": final,
                "variation": list(map(str, variations)), "exception_counts": counts,
                "oscillations": list(map(str, oscillations)),
            }
    raise AssertionError("the proved common-window conclusion failed")


def trim(p):
    p = list(map(Q, p))
    while p and p[-1] == 0:
        p.pop()
    return p


def add(p, q):
    return trim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0)
                 for i in range(max(len(p), len(q)))])


def scale(p, c):
    return trim([c * a for a in p])


def mul(p, q):
    if not p or not q:
        return []
    out = [Q(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return trim(out)


def evaluate(p, x):
    result = Q(0)
    for c in reversed(p):
        result = c + x * result
    return result


def norm(p, r):
    return sum((abs(c) * r**i for i, c in enumerate(p)), Q(0))


def exact_div_linear(p, a):
    """Synthetic division, returning quotient and exact remainder."""
    p = trim(p)
    if len(p) <= 1:
        return [], p[0] if p else Q(0)
    q = [Q(0)] * (len(p) - 1)
    q[-1] = p[-1]
    for i in range(len(p) - 2, 0, -1):
        q[i - 1] = p[i] + a * q[i]
    return trim(q), p[0] + a * q[0]


def sqrt_branch(order):
    """Truncated iteration for Q(X,Z)=(X-Z^2)/2, not a square-root oracle."""
    z = []
    for _ in range(order):
        z = scale(add([0, 1], scale(mul(z, z), -1)), Q(1, 2))[:order + 1]
        z = trim(z)
    return z


def root_series_checks():
    r, s, derivative = Q(1, 32), Q(1, 8), Q(2)
    max_order = 20
    coefficients = sqrt_branch(max_order)
    norm_checks = residual_checks = stability_checks = tail_checks = 0
    binomial = Q(1)
    for k in range(1, max_order + 1):
        binomial *= (Q(1, 2) - (k - 1)) / k
        assert coefficients[k] == binomial
    for k in range(max_order + 1):
        z = sqrt_branch(k)
        assert norm(z, r) <= s
        norm_checks += 1
        for n in range(k, max_order + 1):
            zn = sqrt_branch(n)
            assert z == trim(zn[:k + 1])
            stability_checks += 1
            for x in (0, r / 2, -r / 2, r / 3):
                assert abs(evaluate(add(zn, scale(z, -1)), x)) <= s * Q(1, 2)**(k + 1)
                tail_checks += 1
        residual = add(add(scale(z, 2), mul(z, z)), [0, -1])
        assert all(c == 0 for c in residual[:k + 1])
        assert norm(residual, r) <= derivative * 2 * s
        for x in (r / 2, -r / 2, r / 3, Q(0)):
            assert abs(evaluate(residual, x)) <= derivative * s * Q(1, 2)**k
            residual_checks += 1
    return {"orders": max_order + 1, "weighted_norm_checks": norm_checks,
            "coefficient_stability_checks": stability_checks,
            "finite_tail_checks": tail_checks, "residual_checks": residual_checks,
            "r": str(r), "s": str(s),
            "first_eight_nonconstant_coefficients": list(map(str, coefficients[1:9]))}


def fiber_certificate(f, A, B, points):
    points = [(Q(x), Q(y)) for x, y in points]
    assert len(set(points)) == len(points)
    f, A, B = trim(f), trim(A), trim(B)
    assert f and (len(f) - 1) % 2 == 1 and (A or B)
    N = add(mul(A, A), scale(mul(f, mul(B, B)), -1))
    assert N
    groups = {}
    for x, y in points:
        assert y*y == evaluate(f, x)
        assert evaluate(A, x) + evaluate(B, x)*y == 0
        groups.setdefault(x, []).append(y)
    remaining = N
    factors = []
    for x, ys in groups.items():
        assert len(ys) <= 2
        if len(ys) == 2:
            assert evaluate(A, x) == evaluate(B, x) == 0
        for _ in ys:
            remaining, rem = exact_div_linear(remaining, x)
            assert rem == 0
            factors.append(x)
    assert len(points) <= len(N) - 1
    return {"points": [[str(x), str(y)] for x, y in points],
            "norm_polynomial": list(map(str, N)), "norm_degree": len(N)-1,
            "removed_factors": list(map(str, factors)),
            "residual_polynomial": list(map(str, remaining))}


# Sparse bivariate polynomials: (x-exponent, y-exponent) -> rational coefficient.
def badd(p, q):
    r = dict(p)
    for monomial, coefficient in q.items():
        r[monomial] = r.get(monomial, Q(0)) + coefficient
    return {m: c for m, c in r.items() if c}


def bscale(p, c):
    return {m: c*a for m, a in p.items() if c*a}


def bmul(p, q):
    r = {}
    for (i, j), a in p.items():
        for (k, l), b in q.items():
            m = i+k, j+l
            r[m] = r.get(m, Q(0)) + a*b
    return {m: c for m, c in r.items() if c}


def beval(p, x, y):
    return sum((c*x**i*y**j for (i, j), c in p.items()), Q(0))


def determinant(matrix):
    """Exact rational elimination, including row-swap signs."""
    a = [list(map(Q, row)) for row in matrix]
    n = len(a)
    d = Q(1)
    for i in range(n):
        pivot = next((j for j in range(i, n) if a[j][i]), None)
        if pivot is None:
            return Q(0)
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            d = -d
        v = a[i][i]
        d *= v
        for j in range(i+1, n):
            ratio = a[j][i] / v
            for k in range(i, n):
                a[j][k] -= ratio*a[i][k]
    return d


def quotient_certificate_checks():
    one, x, y = {(0, 0): Q(1)}, {(1, 0): Q(1)}, {(0, 1): Q(1)}
    xy = bmul(x, y)
    F1 = {(0, 2): Q(1), (3, 0): Q(-1), (1, 0): Q(1), (0, 0): Q(-1)}
    F2 = {(2, 0): Q(1), (1, 0): Q(-1)}
    # (variable, basis element, reduced polynomial, coefficient of F1, coefficient of F2)
    identities = [
        (x, one, x, {}, {}), (x, x, x, {}, one),
        (x, y, xy, {}, {}), (x, xy, xy, {}, y),
        (y, one, y, {}, {}), (y, x, xy, {}, {}),
        (y, y, one, one, badd(x, one)),
        (y, xy, x, x, bmul(x, badd(x, one))),
    ]
    for v, b, reduced, u1, u2 in identities:
        left = badd(bmul(v, b), bscale(reduced, -1))
        right = badd(bmul(u1, F1), bmul(u2, F2))
        assert left == right
    points = [(Q(0), Q(1)), (Q(0), Q(-1)), (Q(1), Q(1)), (Q(1), Q(-1))]
    for px, py in points:
        assert beval(F1, px, py) == beval(F2, px, py) == 0
    basis = [one, x, y, xy]
    matrix = [[beval(b, px, py) for b in basis] for px, py in points]
    det = determinant(matrix)
    assert det != 0
    return {"border_identities_verified": len(identities), "dimension_bound": 4,
            "attaining_points": [[str(px), str(py)] for px, py in points],
            "evaluation_determinant": str(det)}


def stability_checks():
    # Exhaust all binary tables of length eight. Their actual finite variation
    # is an admissible budget, so no assumption of monotonicity is made.
    checked = 0
    for bits in product((0, 1), repeat=8):
        def sequence(n, bits=bits):
            return Q(bits[min(n, len(bits)-1)])
        total = sum(abs(bits[t+1]-bits[t]) for t in range(7))
        result = common_window([sequence], [Q(1, 2)], [Q(total)], [], [], lambda n: 1)
        assert result["selected_index"] <= result["budget"]
        checked += 1
    a = lambda n: Q(min(n, 12), 12)
    b = lambda n: Q(min(max(n-5, 0), 7), 7)
    example = common_window([a, b], [Q(1, 4)]*2, [Q(1)]*2,
                            [lambda n: n in (0, 100)], [2], lambda n: n+1)
    assert example["budget"] == 10 and example["start_bound"] == 2046
    vacuous = common_window([], [], [], [], [], lambda n: 0)
    assert vacuous["selected_index"] == vacuous["budget"] == 0
    rejected = 0
    for args in [([lambda n: Q(n)], [Q(1, 2)], [Q(0)], [], [], lambda n: 2),
                 ([], [], [], [lambda n: True], [0], lambda n: 0)]:
        try:
            common_window(*args)
        except ValueError:
            rejected += 1
    assert rejected == 2
    return {"exhaustive_binary_tables": checked, "invalid_contracts_rejected": rejected,
            "simultaneous_example": example, "vacuous_example": vacuous}


def main():
    output = {
        "scope": "Exact finite validation, not universal mathematical or iPRA proof",
        "common_windows": stability_checks(),
        "simple_branch": root_series_checks(),
        "hyperelliptic_sharp_example": fiber_certificate([1,-1,0,1], [0,-1,1], [],
                                      [(0,1),(0,-1),(1,1),(1,-1)]),
        "hyperelliptic_nonzero_B_example": fiber_certificate([1,0,0,1], [], [0,1],
                                      [(0,1),(0,-1),(-1,0)]),
        "finite_algebra_certificate": quotient_certificate_checks(),
    }
    destination = Path(__file__).resolve().parents[1]/"verification"/"exact_checks.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(output, indent=2)+"\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
