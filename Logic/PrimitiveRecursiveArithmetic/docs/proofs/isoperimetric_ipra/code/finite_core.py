#!/usr/bin/env python3
"""Exact rational reference algorithms for the accompanying iPRA argument.

This is an executable specification and a finite-instance checker, not an
implementation of an iPRA proof kernel and not a substitute for the universal
proof in the report. No floating point or trigonometric routine is used.
"""

from fractions import Fraction as Q
from math import isqrt


def dyadic(k):
    assert isinstance(k, int) and k >= 0
    return Q(1, 1 << k)


def sqrt_down(x, t):
    """floor(2**t * sqrt(x)) / 2**t, using only integer arithmetic."""
    x = Q(x)
    if x < 0:
        raise ValueError("sqrt_down requires a nonnegative rational")
    scale = 1 << t
    j = isqrt((x.numerator * scale * scale) // x.denominator)
    y = Q(j, scale)
    assert y * y <= x < (y + Q(1, scale)) ** 2
    return y


def sqrt_up(x, t):
    x = Q(x)
    y = sqrt_down(x, t)
    return y if y * y == x else y + dyadic(t)


def pi_lower(k):
    """The rational ell_k defined in Section 4 of the report."""
    r, t = k + 4, 4 * k + 16
    h = dyadic(t)
    c_hat = Q(0)
    for _ in range(r - 1):
        c_hat = sqrt_down((1 + c_hat) / 2, t)
    c_bar = min(Q(1), c_hat + 2 * h)
    return (1 << r) * sqrt_down(1 - c_bar * c_bar, t)


def polygon(points):
    return [(Q(x), Q(y)) for x, y in points]


def edges(p):
    if not p:
        return []
    return list(zip(p, p[1:] + p[:1]))


def det(p, q):
    return p[0] * q[1] - p[1] * q[0]


def norm_sq_edge(p, q):
    return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2


def signed_area(p):
    return sum((det(a, b) for a, b in edges(p)), Q(0)) / 2


def upper_lengths(p, precision):
    return [sqrt_up(norm_sq_edge(a, b), precision) for a, b in edges(p)]


def lower_lengths(p, precision):
    return [sqrt_down(norm_sq_edge(a, b), precision) for a, b in edges(p)]


def valid(p, u):
    return bool(p) and len(p) == len(u) and all(
        s >= 0 and norm_sq_edge(a, b) <= s * s
        for (a, b), s in zip(edges(p), u)
    )


def ceil_q(x):
    return -((-x.numerator) // x.denominator)


def ceiling_log2(n):
    assert n >= 1
    return (n - 1).bit_length()


def subdivision_budget(p, u, k):
    """Return the explicit finite mesh witness, without allocating its vertices."""
    if not valid(p, u):
        raise ValueError("invalid polygon or certified upper lengths")
    S = sum(u, Q(0))
    if S == 0:
        assert signed_area(p) == 0
        return {"zero_perimeter": True}
    m = len(p)
    B = max(1, ceil_q(S))
    threshold = m * (1 + (1 << k) * B * B)
    R = max(k + 4, ceiling_log2(threshold))
    N = 1 << R
    T = N - m
    counts = [1 + (T * s / S).numerator // (T * s / S).denominator
              for s in u]
    M = sum(counts)
    energy = sum((norm_sq_edge(a, b) / c
                  for (a, b), c in zip(edges(p), counts)), Q(0))
    assert N > m and M <= N
    assert all(c >= 1 and c * S >= T * s for c, s in zip(counts, u))
    assert energy <= S * S / T
    assert m * S * S / T <= dyadic(k)
    return dict(zero_perimeter=False, m=m, B=B, R=R, N=N, T=T,
                counts=counts, repeated_vertices=N-M, energy=energy,
                energy_bound=S*S/T, final_error=m*S*S/T)


def refined_polygon(p, certificate, cap=100000):
    """Materialize the mesh only when it is small enough for a diagnostic."""
    if certificate["zero_perimeter"]:
        return p
    N = certificate["N"]
    if N > cap:
        raise ValueError("mesh exceeds diagnostic allocation cap")
    result = []
    for (a, b), count in zip(edges(p), certificate["counts"]):
        for j in range(count):
            result.append((a[0] + Q(j, count) * (b[0] - a[0]),
                           a[1] + Q(j, count) * (b[1] - a[1])))
    result.extend([result[0]] * certificate["repeated_vertices"])
    assert len(result) == N
    return result


def check_instance(p, u, k):
    """Check exact finite arithmetic and the actual final rational inequality."""
    if not valid(p, u):
        raise ValueError("invalid input")
    S, A = sum(u, Q(0)), abs(signed_area(p))
    witness = subdivision_budget(p, u, k)
    left = 4 * pi_lower(k) * A
    right = S*S + dyadic(k)
    assert left <= right
    return witness, left, right


def arctan_interval_inverse(q, pairs=32):
    """Alternating-series rational enclosure, used ONLY as a cross-check."""
    x = Q(1, q)
    even = sum(((-1)**j * x**(2*j+1) / (2*j+1)
                for j in range(2*pairs)), Q(0))
    return even, even + x**(4*pairs+1) / (4*pairs+1)


def machin_pi_interval(pairs=32):
    """Independent classical Machin enclosure for diagnostic comparisons."""
    a, b = arctan_interval_inverse(5, pairs)
    c, d = arctan_interval_inverse(239, pairs)
    return 16*a - 4*d, 16*b - 4*c


def fraction_json(q):
    q = Q(q)
    return {"numerator": str(q.numerator), "denominator": str(q.denominator)}

