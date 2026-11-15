"""Exact finite arithmetic supporting the manuscript; not an iPRA proof.

All mathematical checks use integers and fractions.  The astronomical general
Khintchine cutoff is intentionally not evaluated.  Every enumeration is bounded.
"""
from fractions import Fraction as F
from math import gcd, isqrt


def ceil_fraction(x):
    return -(-x.numerator // x.denominator)


def convergents(digits):
    """Convergents of a supplied finite regular continued-fraction prefix."""
    p0, p1, q0, q1 = 0, 1, 1, 0
    result = []
    for j, a in enumerate(digits):
        if not isinstance(a, int) or (j and a < 1):
            raise ValueError("Integral digits; positive after the first")
        p, q = a * p1 + p0, a * q1 + q0
        result.append((p, q))
        p0, p1, q0, q1 = p1, p, q1, q
    return result


def denominator_pair(u, v, w):
    """Return 0 for (u,v), 1 for (v,w), with S^2 > 5."""
    if not (1 <= u <= v and w >= u + v and gcd(u, v) == 1):
        raise ValueError("Denominator lemma hypotheses fail")
    h = v * v - u * v - u * u
    assert h != 0
    pair = 0 if h > 0 else 1
    r, s = (u, v) if pair == 0 else (v, w)
    assert (r * r + s * s) ** 2 > 5 * r * r * s * s
    return pair


def sqrt_name(n, precision):
    """Lower dyadic name for sqrt(n), with error strictly below 2^-precision."""
    scale = 1 << precision
    z = isqrt(n * scale * scale)
    assert z * z <= n * scale * scale < (z + 1) ** 2
    return F(z, scale)


def phi_name(precision):
    return (1 + sqrt_name(5, precision)) / 2


def hurwitz_certificate(name, digits, bound):
    """A checked certificate, conditional on the supplied name/CF matching.

    The samples use known periodic prefixes.  This routine does not implement
    the manuscript's general extraction from an irrationality modulus.
    """
    cs = convergents(digits)
    if len(cs) < bound + 4:
        raise ValueError("Need digits through index B+3")
    triple = cs[bound + 1:bound + 4]
    pair = denominator_pair(*(q for _, q in triple))
    candidates = triple[pair:pair + 2]
    u, v = (q for _, q in candidates)
    C = F(u * v, u * u + v * v)
    d = 1 - 5 * C * C
    Q = max(u, v)
    precision = ceil_fraction(100 * Q * Q / d).bit_length()
    eps = F(1, 1 << precision)
    assert Q * Q * eps <= d / 100
    y = name(precision)
    p, q = min(candidates, key=lambda pq: pq[1] ** 2 * abs(y - F(*pq)))
    upper = q * q * (abs(y - F(p, q)) + eps)
    lhs = 5 * upper * upper
    assert bound < q and gcd(p, q) == 1 and lhs < 1
    return {"B": bound, "p": p, "q": q, "precision": precision,
            "normalized_error_upper": upper, "certificate_lhs": lhs}


def open_components(intervals):
    """Clip to [0,1] and merge STRICT overlaps; touching endpoints remain holes.

    Endpoint singletons at 0 and 1 are conservatively retained in the residual,
    even when an unclipped original interval covers them.  This affects no length.
    Optional labels after the first two tuple entries are ignored here.
    """
    clipped = sorted((max(F(0), z[0]), min(F(1), z[1]))
                     for z in intervals if max(F(0), z[0]) < min(F(1), z[1]))
    merged = []
    for a, b in clipped:
        if merged and a < merged[-1][1]:
            merged[-1] = (merged[-1][0], max(b, merged[-1][1]))
        else:
            merged.append((a, b))
    return merged


def union_length(intervals):
    return sum((b - a for a, b in open_components(intervals)), F(0))


def residual_closed_gaps(intervals):
    """Include every closed residual gap, including singleton touching points."""
    gaps, cursor = [], F(0)
    for a, b in open_components(intervals):
        if cursor <= a:
            gaps.append((cursor, a))
        cursor = b
    if cursor <= 1:
        gaps.append((cursor, F(1)))
    return gaps


def intersection_length(left, right):
    a, b = open_components(left), open_components(right)
    i = j = 0
    total = F(0)
    for _ in range(len(a) + len(b)):
        if i == len(a) or j == len(b):
            break
        total += max(F(0), min(a[i][1], b[j][1]) - max(a[i][0], b[j][0]))
        if a[i][1] <= b[j][1]:
            i += 1
        else:
            j += 1
    return total


def approximation_intervals(psi, N, M):
    """All reduced labels p/q, N<=q<=M, 0<=p<=q; tuple=(lo,hi,p,q)."""
    if not 1 <= N <= M:
        raise ValueError("Require 1 <= N <= M")
    result = []
    for q in range(N, M + 1):
        radius = F(psi(q)) / q
        if radius < 0:
            raise ValueError("Nonnegative approximation function required")
        if radius == 0:
            continue
        for p in range(q + 1):
            if gcd(p, q) == 1:
                x = F(p, q)
                result.append((x - radius, x + radius, p, q))
    return result


def local_centers(J, k):
    """Reduced fractions in the middle half of J, with 2^k/4<q<=2^k."""
    a, b = map(F, J)
    if not (0 <= a < b <= 1 and k >= 2):
        raise ValueError("Require nonempty J in [0,1] and k>=2")
    L, Q = b - a, 1 << k
    lo, hi = a + L / 4, b - L / 4
    centers = []
    for q in range(Q // 4 + 1, Q + 1):
        for p in range(q + 1):
            if gcd(p, q) == 1 and lo < F(p, q) < hi:
                centers.append(F(p, q))
    return centers


def local_block(J, k, psi):
    Q = 1 << k
    t = min(Q * F(psi(Q)), F(1))
    if t < 0:
        raise ValueError("Nonnegative approximation function required")
    centers = local_centers(J, k)
    radius = t / (8 * Q * Q)
    intervals = [(x - radius, x + radius) for x in centers] if t else []
    return {"k": k, "Q": Q, "t": t, "radius": radius,
            "centers": centers, "intervals": intervals}
