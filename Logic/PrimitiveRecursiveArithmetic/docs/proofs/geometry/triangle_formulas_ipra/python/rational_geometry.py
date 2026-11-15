"""Exact rational certificates for the quantitative triangle theorems.

All computations use integers and Fraction; no floating-point arithmetic.
The bounded root routine implements the specification in the report.  These
programs provide executable evidence, not a formal proof of iPRA derivability.
"""

from fractions import Fraction as F


def pow2neg(k):
    assert isinstance(k, int) and k >= 0
    return F(1, 1 << k)


def root_floor(q, k):
    """Largest j/2**k whose square is <= q, using a bounded binary search."""
    q = F(q)
    assert q >= 0 and k >= 0
    p, den = q.numerator, q.denominator
    scale = 1 << k
    bound = (p + 1) * scale
    target = p * scale * scale
    lo, hi = 0, bound
    # This loop has an input-computable, primitive-recursive bound.
    for _ in range(bound.bit_length() + 1):
        mid = (lo + hi + 1) // 2
        if den * mid * mid <= target:
            lo = mid
        else:
            hi = mid - 1
    assert lo == hi
    assert den * lo * lo <= target < den * (lo + 1) ** 2
    return F(lo, scale)


def root_floor_scan(q, k):
    """Literal bounded-scan specification, intended only for small examples."""
    q = F(q)
    assert q >= 0
    p, den = q.numerator, q.denominator
    scale = 1 << k
    r = 0
    for j in range((p + 1) * scale + 1):
        if den * j * j <= p * scale * scale:
            r = j
    return F(r, scale)


def ceil_fraction(x):
    x = F(x)
    return -(-x.numerator // x.denominator)


def ceil_log2_positive(q):
    """Least d >= 0 with 2**d >= q, for a positive rational q."""
    q = F(q)
    assert q > 0
    d = max(0, q.numerator.bit_length() - q.denominator.bit_length())
    if F(1 << d) < q:
        d += 1
    assert F(1 << d) >= q
    assert d == 0 or F(1 << (d - 1)) < q
    return d


def invariants(coords):
    x, y, z, w = map(F, coords)
    U = x*x + y*y
    V = z*z + w*w
    W = (x-z)**2 + (y-w)**2
    p = x*z + y*w
    t = x*w - y*z
    assert W == U + V - 2*p
    assert U*V == p*p + t*t
    return x, y, z, w, U, V, W, p, t


def finite_heron(coords, k, M=None):
    """The report's all-rational Heron theorem, including degenerate triples."""
    x, y, z, w, U, V, W, p, t = invariants(coords)
    if M is None:
        M = max(1, *(ceil_fraction(abs(v)) for v in (x, y, z, w)))
    assert isinstance(M, int) and M >= 1
    assert max(map(abs, (x, y, z, w))) <= M
    Q = 4*M
    assert max(U, V, W) <= Q*Q
    n = 2*k + 4 + 3*Q
    a, b, c = (root_floor(q, n) for q in (W, V, U))
    eps = pow2neg(n)
    for q, r in ((W, a), (V, b), (U, c)):
        assert 0 <= r <= Q
        assert 0 <= q-r*r <= 3*Q*eps
    s = (a+b+c)/2
    P = s*(s-a)*(s-b)*(s-c)
    area = abs(t)/2
    assert abs(P-area*area) <= 4*Q**3*eps
    assert 4*Q**3*eps <= pow2neg(2*k+2)
    clipped = max(P, F(0))
    assert abs(clipped-area*area) <= pow2neg(2*k+2)
    result = root_floor(clipped, k+1)
    error = abs(result-area)
    assert error <= pow2neg(k)
    return {"requested_precision": k, "internal_precision": n,
            "Q": Q, "area": area, "approximation": result,
            "error": error, "bound": pow2neg(k),
            "intermediate_radicand": P}


def finite_trigonometry(coords, k, M=None, d=None):
    """All-rational cosine and extended-sine residuals with apartness data."""
    x, y, z, w, U, V, W, p, t = invariants(coords)
    h = abs(t)
    assert h > 0, "The divided sine law requires determinant apartness."
    if M is None:
        M = max(1, *(ceil_fraction(abs(v)) for v in (x, y, z, w)))
    if d is None:
        d = ceil_log2_positive(1/h)
    assert isinstance(M, int) and M >= 1
    assert isinstance(d, int) and d >= 0
    assert max(map(abs, (x, y, z, w))) <= M
    assert h >= pow2neg(d)
    Q = 4*M
    n = 2*k + 2*d + 5*Q + 8
    eps = pow2neg(n)
    a, b, c = (root_floor(q, n) for q in (W, V, U))
    lower = pow2neg(d)/(2*Q)
    assert min(a, b, c) >= lower > 0
    cosA, cosB, cosC = p/(b*c), (U-p)/(c*a), (V-p)/(a*b)
    sinA, sinB, sinC = h/(b*c), h/(c*a), h/(a*b)
    cos_residuals = (
        a*a-b*b-c*c+2*b*c*cosA,
        b*b-c*c-a*a+2*c*a*cosB,
        c*c-a*a-b*b+2*a*b*cosC,
    )
    assert all(abs(r) <= 9*Q*eps <= pow2neg(k) for r in cos_residuals)
    K = a*b*c/h
    assert a/sinA == b/sinB == c/sinC == K
    ox, oy = (U*w-V*y)/(2*t), (V*x-U*z)/(2*t)
    radius_sq = ox*ox + oy*oy
    assert (ox-x)**2+(oy-y)**2 == radius_sq
    assert (ox-z)**2+(oy-w)**2 == radius_sq
    assert 4*h*h*radius_sq == U*V*W
    square_residual = 4*radius_sq-K*K
    assert 0 <= square_residual <= 9*Q**5*pow2neg(n)*2**(2*d)
    assert square_residual <= pow2neg(2*k+4)
    radius_approx = root_floor(radius_sq, k+2)
    extended_sine_error = abs(K-2*radius_approx)
    assert extended_sine_error <= pow2neg(k)
    return {"requested_precision": k, "internal_precision": n,
            "Q": Q, "apartness_exponent": d,
            "cosine_residuals": cos_residuals,
            "sine_ratios_exactly_equal": True,
            "circumcenter": (ox, oy), "radius_squared": radius_sq,
            "extended_sine_error": extended_sine_error,
            "bound": pow2neg(k)}


def json_safe(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {k: json_safe(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [json_safe(v) for v in value]
    return value
