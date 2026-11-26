"""Independent high-precision numerical cross-check, through a group determinant.

Unlike the certification, this check does not isolate individual characters.
Requires mpmath. The finite-difference approximations are numerical evidence.
"""
from math import gcd
from mpmath import mp

mp.dps = 100
q = 15
units = [a for a in range(1, q) if gcd(a, q) == 1]


def regularized_zeta(h):
    s = 1 + h
    progressions = {a: mp.zeta(s, mp.mpf(a) / q) / q**s for a in units}
    group_matrix = mp.matrix([[progressions[a * pow(b, -1, q) % q]
                               for b in units] for a in units])
    # At 3 there is a single prime of residue degree 4.
    # At 5 there is a single prime of residue degree 2.
    omitted = (1 - mp.power(3, -4*s)) * (1 - mp.power(5, -2*s))
    return h * mp.det(group_matrix) / omitted


disc = 15**8 // (3**4 * 5**2)
for exponent in (5, 8, 12):
    h = mp.power(10, -exponent)
    ek = (mp.log(regularized_zeta(h)) - mp.log(regularized_zeta(-h))) / (2*h)
    B = 2 + 2*ek + mp.log(disc) - 8*(mp.log(2*mp.pi) + mp.euler)
    print(f"h = 1e-{exponent}: gamma_K ~ {mp.nstr(ek, 24)}, B_K ~ {mp.nstr(B, 24)}")
