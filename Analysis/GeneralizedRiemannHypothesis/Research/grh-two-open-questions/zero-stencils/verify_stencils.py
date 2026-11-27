"""Check the integer identities and directed-rounded intervals in the paper.

Run with Python 3 and mpmath (tested with mpmath 1.3.0).
"""
from mpmath import iv

iv.dps = 65

# Each stencil coefficient is represented by its coefficients of a and b.
weights = [(1, 0), (-2, 1), (1, -2), (0, 1)]
for coordinate in (0, 1):
    assert sum(w[coordinate] for w in weights) == 0
    assert sum(i * w[coordinate] for i, w in enumerate(weights)) == 0

correlations = []
for lag in (1, 2, 3):
    aa = ab = bb = 0
    for (a, b), (c, d) in zip(weights, weights[lag:]):
        aa += a * c
        ab += a * d + b * c
        bb += b * d
    correlations.append((aa, ab, bb))
assert correlations == [(-4, 7, -4), (1, -4, 1), (0, 1, 0)]
assert tuple(sum(lag**3 * correlations[lag-1][i] for lag in (1, 2, 3))
             for i in (0, 1, 2)) == (4, 2, 4)
print("Verified exact autocorrelations and the normalization at zero.")

def acos_interval(x):
    """On (-1,1) use an interval atan2 and positive square root."""
    assert x > -1 and x < 1
    return iv.atan2(iv.sqrt(1-x*x), x)

def triangle_angles(t):
    A, B, C = 4 - 7*t, 8 - 32*t, 27*t
    u = acos_interval((A*A+B*B-C*C)/(2*A*B))
    v = -acos_interval((A*A+C*C-B*B)/(2*A*C))
    return u, v

alpha = iv.log(3)/iv.log(2)

def phase_residual(t):
    u, v = triangle_angles(t)
    return (v-alpha*u)/(2*iv.pi) - (1-alpha)

t_lower = "0.16788340058442558"
t_upper = "0.16788340058442560"
t = iv.mpf([t_lower, t_upper])
for endpoint, sign in ((t_lower, 1), (t_upper, -1)):
    residual = phase_residual(iv.mpf(endpoint))
    assert sign * residual > 0
    print(f"Residual at t={endpoint} has sign {sign:+d}: {iv.nstr(residual, 12)}")
u, v = triangle_angles(t)
omega = (2*iv.pi-u)/iv.log(2)
assert omega > iv.mpf("6.23399540333078")
assert omega < iv.mpf("6.23399540333080")
assert omega > 2*iv.pi/iv.log(3)
assert omega < 3*iv.pi/(2*iv.log(2))
print("Certified missing frequency:", iv.nstr(omega, 18))
radius = iv.mpf("0.1604")/iv.sqrt(1+omega**2)
assert radius > iv.mpf("0.02540510624516730")
assert radius < iv.mpf("0.02540510624516734")
print("Certified largest model half-width:", iv.nstr(radius, 18))
