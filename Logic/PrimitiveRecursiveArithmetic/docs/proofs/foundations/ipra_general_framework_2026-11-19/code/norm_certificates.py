#!/usr/bin/env python3
"""Exact experiments for the norm theorems; not a proof of universal claims.

The main norm uses monic remainders and the literal Leibniz formula.
An independent SymPy resultant is used as a comparison.  No roots,
floating-point arithmetic, factorization oracle, or randomized sampling
of real values is used.  Test generation is deterministic.
"""
from __future__ import annotations
import itertools
import json
import math
import random
from pathlib import Path
import sympy as sp

X, Y, T, U = sp.symbols("X Y T U")


def determinant_leibniz(matrix):
    n = len(matrix)
    out = sp.Integer(0)
    for perm in itertools.permutations(range(n)):
        factors = [matrix[perm[j]][j] for j in range(n)]
        if any(a == 0 for a in factors):
            continue
        inv = sum(perm[i] > perm[j] for i in range(n) for j in range(i + 1, n))
        out += (-1) ** inv * sp.prod(factors)
    return sp.expand(out)


def multiplication_matrix(F, G, m, variable=Y):
    divisor = sp.Poly(F, variable)
    assert divisor.degree() == m and divisor.LC() == 1
    cols = []
    for j in range(m):
        rem = sp.rem(sp.Poly(sp.expand(G * variable**j), variable), divisor)
        cols.append([sp.expand(rem.nth(i)) for i in range(m)])
    return [[cols[j][i] for j in range(m)] for i in range(m)]


def norm(F, G, m, variable=Y):
    return determinant_leibniz(multiplication_matrix(F, G, m, variable))


def degree(poly, variable=X):
    p = sp.Poly(sp.expand(poly), variable)
    return None if p.is_zero else int(p.degree())


def local_order(poly, point, variable=X):
    shifted = sp.Poly(sp.expand(poly.subs(variable, T + point)), T)
    if shifted.is_zero:
        return None, sp.Integer(0)
    e = min(m[0] for m, c in shifted.terms() if c != 0)
    return e, shifted.nth(e)


def weight(G, m, d):
    rows = sp.Poly(G, Y)
    candidates = []
    for j in range(m):
        a = rows.nth(j)
        n = degree(a)
        if n is not None:
            candidates.append((m * n + d * j, j, sp.Poly(a, X).LC()))
    assert candidates
    return max(w for w, j, c in candidates), candidates


def verify_local(F, G, m, d, point=0):
    rows = sp.Poly(F, Y)
    e, first = local_order(rows.nth(0), point)
    assert e is not None and e > 0 and math.gcd(m, e) == 1
    c = -first
    for j in range(m):
        f = rows.nth(j)
        q = degree(f)
        if q is not None:
            assert m * q + d * j <= m * d
        if j > 0:
            v, _ = local_order(f, point)
            assert v is None or m * v + e * j > m * e
    gs = sp.Poly(G, Y)
    items = []
    for j in range(m):
        v, b = local_order(gs.nth(j), point)
        if v is not None:
            items.append((m * v + e * j, j, b))
    s, k, b = min(items)
    assert sum(w == s for w, j, b0 in items) == 1
    expected = sp.expand(b**m * ((-1) ** (m - 1) * c) ** k)
    n = norm(F, G, m)
    actual_s, actual_c = local_order(n, point)
    W, _ = weight(G, m, d)
    assert degree(n) is not None and degree(n) <= W
    assert actual_s == s and sp.expand(actual_c - expected) == 0
    resultant = sp.expand(sp.resultant(F, G, Y))
    assert sp.expand(n - resultant) == 0
    return {"m": m, "d": d, "a": str(point), "e": e, "s": s,
            "W": W, "norm_degree": degree(n), "initial": str(expected)}


def verify_compressed(f, G, m, d):
    W, rows = weight(G, m, d)
    c = sp.Poly(f, X).LC()
    H = sum(b * Y**j for w, j, b in rows if w == W)
    g = math.gcd(m, d)
    r = m // g
    active = [(j, b) for w, j, b in rows if w == W]
    j0 = active[0][0] % r
    assert all(j % r == j0 for j, b in active)
    P = sum(b * U ** ((j - j0) // r) for j, b in active)
    small = norm(U**g - c, P, g, U)
    expected = sp.expand(((-1) ** (m - 1) * c) ** j0 * small**r)
    direct = norm(Y**m - c, H, m)
    full = norm(Y**m - f, G, m)
    actual = sp.Poly(full, X).nth(W)
    assert sp.expand(expected - direct) == 0
    assert sp.expand(actual - expected) == 0
    return {"m": m, "d": d, "small_dimension": g, "W": W,
            "H": str(H), "P": str(P), "small_norm": str(small),
            "leading_coefficient": str(expected)}


def verify_squarefree(f, G, m):
    """Perform the universal-root algebra calculation, including zero divisors."""
    d = degree(f)
    assert d is not None and d >= 1
    deriv = sp.diff(f, X)
    assert degree(sp.gcd(f, deriv)) == 0
    fU = f.subs(X, U)

    def red(a):
        return sp.expand(sp.rem(sp.Poly(a, U), sp.Poly(fU, U)).as_expr())

    def shifted_coeffs(a):
        p = sp.Poly(sp.expand(a.subs(X, U + T)), T)
        return [red(p.nth(i)) for i in range(int(p.degree()) + 1)] if not p.is_zero else []

    c = red(deriv.subs(X, U))
    c_inv = sp.invert(c, fU, U)
    assert red(c * c_inv) == 1
    entries = []
    for j in range(m):
        coeffs = shifted_coeffs(sp.Poly(G, Y).nth(j))
        for v, b in enumerate(coeffs):
            if b != 0:
                entries.append((m * v + j, j, b))
                break
    s, k, b = min(entries)
    expected = red(b**m * ((-1) ** (m - 1) * c) ** k)
    assert expected != 0
    n = norm(Y**m - f, G, m)
    coeffs = shifted_coeffs(n)
    assert all(v == 0 for v in coeffs[:s])
    assert sp.expand(coeffs[s] - expected) == 0
    assert sp.expand(n - sp.resultant(Y**m - f, G, Y)) == 0
    W, _ = weight(G, m, d)
    assert degree(n) is not None and degree(n) <= W
    return {"f": str(f), "G": str(G), "m": m, "degree_f": d,
            "universal_local_order": s, "leading_element": str(expected),
            "norm": str(sp.factor(n)), "norm_degree": degree(n), "W": W}


def run_validation():
    rng = random.Random(20261119)
    local_cases = []
    compressed_cases = []
    # Mixed equations with explicit one-edge local Newton certificates.
    for m in range(1, 5):
        for e in range(1, 4):
            if math.gcd(m, e) != 1:
                continue
            for d in range(e + 1, e + 4):
                for a in [sp.Integer(0), sp.Rational(1, 2)]:
                    Z = X - a
                    F = Y**m - (Z**d + Z**e)
                    for j in range(1, m):
                        low = (m * e - e * j) // m + 1
                        high = d * (m - j) // m
                        if low <= high:
                            F += rng.choice([-2, -1, 0, 1, 2]) * Z**low * Y**j
                    G = sum(sum(rng.randint(-2, 2) * Z**i for i in range(3)) * Y**j
                            for j in range(m))
                    if sp.expand(G) == 0:
                        G = sp.Integer(1)
                    local_cases.append(verify_local(sp.expand(F), sp.expand(G), m, d, a))
    # Both successful leading certificates and exact top cancellation.
    for m in range(2, 6):
        for d in range(2, 7):
            f = X**d + X
            for sgn in [-1, 1]:
                r = m // math.gcd(m, d)
                G = sgn * X ** (d // math.gcd(m, d)) + (Y**r if r < m else Y)
                compressed_cases.append(verify_compressed(f, G, m, d))
    compressed_cases.append(verify_compressed(X**4 + X, Y**3 + 2 * X**2, 6, 4))
    examples = []
    for F, G, m, d in [
        (Y**2 - X**4 - X, Y - X**2, 2, 4),
        (Y**3 - X**6 - X, Y - X**2, 3, 6),
        (Y**2 + X*Y - X**4 - X, Y - X**2, 2, 4),
        (Y**6 - X**4 - X, Y**3 + 2*X**2, 6, 4),
    ]:
        v = verify_local(F, G, m, d)
        examples.append({"F": str(F), "G": str(G), "norm": str(sp.factor(norm(F,G,m))), **v})
    # Fiber multiplicity, including a ramified fiber of cardinality one.
    F = Y**2 - (X**4-X**2+X)
    G = X*(X-1)
    points = [(0,0), (1,1), (1,-1)]
    assert all(F.subs({X:a,Y:b}) == G.subs({X:a,Y:b}) == 0 for a,b in points)
    n = norm(F,G,2)
    factor = X*(X-1)**2
    assert sp.rem(n, factor, X) == 0
    assert len(points) <= degree(n)
    # Required failure mode when no nonvanishing certificate is valid.
    assert norm(Y**2-X**4, Y-X**2, 2) == 0
    squarefree_cases = []
    for f in [X**2+1, X*(X-1), X**4+1, X**3-X, 2*X**3+X+1]:
        for m in range(1, 5):
            for G in [sp.Integer(1), f, (Y-X**2 if m > 1 else X-1),
                      ((X-1)+X*Y if m > 1 else X+1)]:
                squarefree_cases.append(verify_squarefree(f, G, m))
    # A non-squarefree input with no useful rational local root:
    # g=X^2+1, e=3, h=(X+2)^2, m=4.  All global top terms cancel.
    g = X**2 + 1
    h = (X+2)**2
    f = g**3 * h
    G = g**2 + g*Y
    divisor_norm = norm(Y**4-f, G, 4)
    assert sp.expand(divisor_norm - g**7 * (g-h)) == 0
    assert sp.rem(g-h, g, X) != 0 and sp.gcd(g,h) == 1
    assert degree(divisor_norm) == 15 and weight(G,4,8)[0] == 16
    return {
        "status": "passed",
        "arithmetic": "exact symbolic rational polynomial arithmetic",
        "universal_proof": False,
        "local_newton_cases": len(local_cases),
        "compressed_leading_cases": len(compressed_cases),
        "independent_resultant_comparisons": len(local_cases)+len(examples),
        "squarefree_algebra_cases": len(squarefree_cases),
        "squarefree_resultant_comparisons": len(squarefree_cases),
        "general_divisor_example": {"g": str(g), "e": 3, "h": str(h), "m": 4,
                                     "f": str(f), "G": str(G), "norm": str(sp.factor(divisor_norm)),
                                     "division_order": 7, "norm_degree": 15, "weight": 16},
        "fiber_example": {"points": points, "norm": str(sp.factor(n)),
                          "required_divisor": str(factor), "point_count": len(points)},
        "zero_norm_counterexample": "Y^2-X^4, G=Y-X^2",
        "examples": examples,
        "local_cases": local_cases,
        "compressed_cases": compressed_cases,
        "squarefree_cases": squarefree_cases,
    }


if __name__ == "__main__":
    out = run_validation()
    dest = Path(__file__).resolve().parents[1] / "validation" / "norm_validation.json"
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({k:out[k] for k in ["status", "local_newton_cases", "compressed_leading_cases", "independent_resultant_comparisons", "squarefree_algebra_cases"]}))
