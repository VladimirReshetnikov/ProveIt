#!/usr/bin/env python3
"""Illustration with computed critical-line zeros for the units modulo 4.

Requires Python 3 and mpmath (tested with 1.3.0). This script uses ordinary
high-precision arithmetic. It neither certifies the zeros nor counts all
zeros in the interval. No external zero tables are used.
"""

import mpmath as mp


def beta(s):
    """Dirichlet L-function for the primitive odd character modulo 4."""
    return mp.power(4, -s) * (mp.zeta(s, mp.mpf(1) / 4)
                              - mp.zeta(s, mp.mpf(3) / 4))


def hardy_value(t, conductor, parity, lfunction):
    s = mp.mpc(mp.mpf(1) / 2, t)
    phase = (mp.im(mp.loggamma((s + parity) / 2))
             + t * mp.log(conductor / mp.pi) / 2)
    value = mp.expj(phase) * lfunction(s)
    if abs(mp.im(value)) > mp.mpf("1e-35"):
        raise ArithmeticError("Hardy rotation produced an unexpected imaginary part")
    return mp.re(value)


def show_zero(name, endpoints, conductor, parity, function, other):
    left, right = map(mp.mpf, endpoints)
    def hardy(t):
        return hardy_value(t, conductor, parity, function)
    if hardy(left) * hardy(right) >= 0:
        raise ArithmeticError("the specified bracket does not have opposite signs")
    t = mp.findroot(hardy, (left, right), solver="anderson")
    s = mp.mpc(mp.mpf(1) / 2, t)
    residual = abs(function(s))
    slope = abs(mp.diff(hardy, t))
    other_abs = abs(other(s))
    if not (left < t < right and residual < mp.mpf("1e-32")
            and slope > mp.mpf("0.01") and other_abs > mp.mpf("0.01")):
        raise ArithmeticError("numerical root checks failed")
    print(f"{name:5s}  {mp.nstr(t, 19):>22s}  {mp.nstr(slope, 10):>14s}"
          f"  {mp.nstr(other_abs, 10):>14s}       < 1e-32")


if __name__ == "__main__":
    mp.mp.dps = 50
    print(f"Illustrative computation with mpmath {mp.__version__}, 50 decimal digits.")
    print("Two roots in 12.5 < Im(s) < 15; no exhaustive count is asserted.")
    print("L                 Im(root)        |Z'(t)|       |other L|         |L(root)|")
    show_zero("beta", ("12.8", "13.1"), 4, 1, beta, mp.zeta)
    show_zero("zeta", ("14.0", "14.3"), 1, 0, mp.zeta, beta)
    print("Assuming the indicated simple, unshared roots, the character")
    print("multiplicity rows in coordinates (f(1),f(3)) for m=1 are")
    print("beta: (1/2,-1/2); zeta: (1/2,1/2). Their determinant is 1/2.")
    print("For f = delta_1 - delta_3 the zeta row cancels; beta yields 1.")
    print("At m=2 the pullback is constant f(1): only the zeta row survives.")
