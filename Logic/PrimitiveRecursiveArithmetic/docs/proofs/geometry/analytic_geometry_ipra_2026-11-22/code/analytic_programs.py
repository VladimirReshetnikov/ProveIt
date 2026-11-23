"""Exact reference algorithms for the report's finite numerical contracts.

Python integers and Fraction stand for the report's natural/signed/rational
codes. Loops have explicit finite bounds. This executable code is not a Lean
proof or an object-iPRA derivation.
"""
from __future__ import annotations

from fractions import Fraction as Q
from typing import Mapping, Sequence

Poly = Mapping[tuple[int, ...], Q]


def ceil_q(x: Q) -> int:
    return -((-x.numerator) // x.denominator)


def log_ceiling(B: int) -> int:
    if B < 1:
        raise ValueError("B must be positive")
    return (B - 1).bit_length()


def bounded_isqrt(m: int) -> int:
    """Largest j with j*j <= m, using a fixed iteration bound."""
    if m < 0:
        raise ValueError("nonnegative input required")
    lo, hi = 0, m + 1
    for _ in range(m.bit_length() + 1):
        if hi - lo > 1:
            mid = (lo + hi) // 2
            if mid * mid <= m:
                lo = mid
            else:
                hi = mid
    assert lo * lo <= m < hi * hi and hi == lo + 1
    return lo


def sqrt_bracket(q: Q, n: int) -> tuple[Q, Q]:
    if q < 0 or n < 0:
        raise ValueError("nonnegative rational and precision required")
    H = 2**n
    j = bounded_isqrt((q.numerator * H * H) // q.denominator)
    return Q(j, H), Q(j + 1, H)


def trig_polynomial(t: Q, degree: int) -> tuple[Q, Q]:
    """Exact real/imaginary parts of sum_{j<=degree} (i*t)^j/j!."""
    if degree < 0:
        raise ValueError("nonnegative degree required")
    c = s = Q(0)
    term = Q(1)
    for j in range(degree + 1):
        if j % 4 == 0:
            c += term
        elif j % 4 == 1:
            s += term
        elif j % 4 == 2:
            c -= term
        else:
            s -= term
        term *= t / (j + 1)
    return c, s


def sincos_observation(t: Q, n: int, magnitude_bound: int | None = None):
    M = max(1, ceil_q(abs(t))) if magnitude_bound is None else magnitude_bound
    if n < 0 or M < 1 or abs(t) > M:
        raise ValueError("invalid precision or magnitude bound")
    N = 4 * M + n + 6
    return trig_polynomial(t, N), {"M": M, "degree": N, "tail": Q(1, 2 ** (n + 6))}


def poly_eval(poly: Poly, point: Sequence[Q]) -> Q:
    total = Q(0)
    for exponent, coefficient in poly.items():
        if len(exponent) != len(point) or any(e < 0 for e in exponent):
            raise ValueError("invalid polynomial arity/exponent")
        term = Q(coefficient)
        for x, e in zip(point, exponent):
            term *= x**e
        total += term
    return total


def partial(poly: Poly, i: int) -> dict[tuple[int, ...], Q]:
    out: dict[tuple[int, ...], Q] = {}
    for exponent, coefficient in poly.items():
        if exponent[i]:
            e = list(exponent)
            e[i] -= 1
            key = tuple(e)
            out[key] = out.get(key, Q(0)) + coefficient * exponent[i]
    return out


def polynomial_bounds(poly: Poly, M: int):
    if M < 1:
        raise ValueError("M >= 1 required")
    H, B, L = Q(0), Q(1), Q(1)
    for exponent, coefficient in poly.items():
        d = sum(exponent)
        term = abs(coefficient) * (M + 1) ** d
        H += term
        B += d * term
        L += d * d * term
    return H, B, L


def implicit_data(poly: Poly, base: Sequence[Q]):
    """Prepare the theorem's box; last coordinate is the dependent variable."""
    p = tuple(map(Q, base))
    if poly_eval(poly, p) != 0:
        raise ValueError("base must be an exact rational root")
    F = {e: Q(c) for e, c in poly.items()}
    g = poly_eval(partial(F, len(p) - 1), p)
    if g < 0:
        F = {e: -c for e, c in F.items()}
        g = -g
    if g == 0:
        raise ValueError("dependent partial must be nonzero")
    M = max(1, *(ceil_q(abs(x)) for x in p))
    H, B, L = polynomial_bounds(F, M)
    r = min(Q(1), g / (4 * (L + 1)))
    a = g * r / (4 * (B + g + 1))
    return {"poly": F, "base": p, "g": g, "M": M, "H": H, "B": B, "L": L, "r": r, "a": a}


def implicit_observation(data, independent: Sequence[Q], n: int):
    x = tuple(map(Q, independent))
    p = data["base"]
    if n < 0 or len(x) != len(p) - 1:
        raise ValueError("wrong arity or precision")
    if max(abs(u - v) for u, v in zip(x, p[:-1])) > data["a"]:
        raise ValueError("outside certified horizontal box")
    F = data["poly"]
    lo, hi = p[-1] - data["r"], p[-1] + data["r"]
    assert poly_eval(F, x + (lo,)) <= 0 <= poly_eval(F, x + (hi,))
    for _ in range(n + 2):
        mid = (lo + hi) / 2
        if poly_eval(F, x + (mid,)) <= 0:
            lo = mid
        else:
            hi = mid
    return {"lower": lo, "upper": hi, "midpoint": (lo + hi) / 2, "steps": n + 2}


def curve_eval(coefficients: Sequence[Sequence[Q]], t: Q):
    values = []
    for row in coefficients:
        acc = Q(0)
        for c in reversed(row):
            acc = acc * t + c
        values.append(acc)
    return tuple(values)


def polygon_length_bracket(coefficients, a: Q, b: Q, k: int, root_precision: int):
    """Exact lower/upper bracket for a dyadic polygon's chord sum."""
    if not a < b or min(k, root_precision) < 0:
        raise ValueError("invalid interval or precision")
    N = 2**k
    lo = hi = Q(0)
    p = curve_eval(coefficients, a)
    for j in range(N):
        q = curve_eval(coefficients, a + (b - a) * Q(j + 1, N))
        sq = sum((x - y) ** 2 for x, y in zip(p, q))
        l, u = sqrt_bracket(sq, root_precision)
        lo += l
        hi += u
        p = q
    return lo, hi


def curve_bounds(coefficients, a: Q, b: Q):
    M = max(1, ceil_q(abs(a)), ceil_q(abs(b)))
    V = K = Q(0)
    for row in coefficients:
        for j, c in enumerate(row):
            if j >= 1:
                V += abs(c) * j * M ** (j - 1)
            if j >= 2:
                K += abs(c) * j * (j - 1) * M ** (j - 2)
    return V, K
