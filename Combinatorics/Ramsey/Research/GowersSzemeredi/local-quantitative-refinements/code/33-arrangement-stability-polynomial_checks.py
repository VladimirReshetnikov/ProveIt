"""Tiny independent rational polynomial checks; coefficients are ascending."""
from fractions import Fraction as F
from math import comb


def add(a, b):
    return [((a[i] if i < len(a) else 0)+(b[i] if i < len(b) else 0))
            for i in range(max(len(a), len(b)))]


def scale(a, t):
    return [x*t for x in a]


def mul(a, b):
    c = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return c


def verify_polynomials():
    r = [F(0), F(1, 4), F(3, 8), F(1), F(105, 32)]
    rr = mul(r, r)
    composed = add(add(scale(r, 4), scale(rr, -24)), scale(mul(rr, r), 32))
    assert composed[:5] == [0, 1, 0, 0, 0]
    # Substitute delta=1/(2n) into F_4: 2/n-6/n^2+4/n^3.
    for n in range(3, 104, 2):
        delta = F(1, 2*n)
        assert 4*delta-24*delta**2+32*delta**3 == F(2, n)-F(6, n*n)+F(4, n**3)
    # The first two coefficients in the sharp-family expansion.
    for s in range(4, 42, 2):
        linear = F(4*s, 4)
        quadratic = F(-16*comb(s, 2), 4)
        assert linear == s and quadratic == -2*s*(s-1)
        inverse_first, inverse_second = F(1, s), F(2*(s-1), s*s)
        assert s*inverse_first == 1
        assert s*inverse_second-2*s*(s-1)*inverse_first**2 == 0
    return {"cubic_inverse_coefficients": ["1/4", "3/8", "1", "105/32"],
            "sharp_family_linear_quadratic_checked_even_orders_through": 40}
