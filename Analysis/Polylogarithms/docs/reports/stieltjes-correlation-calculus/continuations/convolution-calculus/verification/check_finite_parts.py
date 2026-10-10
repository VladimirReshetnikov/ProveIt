"""Independent endpoint-subtraction checks of Stieltjes correlations.

This file evaluates convergent real integrals directly.  The right-hand sides
are evaluated independently from polylogarithms or generalized Stieltjes
constants. Order derivatives of the polylogarithm use a Cauchy contour because
mpmath 1.3.0's default near-integer finite differences can lose accuracy when
its internal zeta series stops near a trivial zero. These numerical checks
are evidence, not a replacement for proof or certified interval arithmetic.
"""

import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 55


def g0(x):
    return -mp.digamma(x)


def circular00(a):
    """Exact finite part by subtracting the singularity on each interval."""
    b = 1 - a

    def piece(c, length):
        def f(x):
            if abs(x) < mp.mpf("1e-45"):
                return -mp.polygamma(1, c) + mp.euler * g0(c)
            return (g0(c + x) - g0(c)) / x + g0(1 + x) * g0(c + x)

        return mp.quad(f, [0, length / 2, length]) + g0(c) * mp.log(length)

    return piece(a, b) + piece(b, a)


def contour_derivatives(func, center, max_order, nodes=64):
    """Cauchy derivatives with midpoint samples on a radius-1/8 circle.

    The midpoint angles avoid evaluations exactly on the real order axis.
    The node count is checked against independent real quadrature below;
    this is not a formal bound on the trapezoidal aliasing error.
    """
    rho = mp.mpf("0.125")
    sums = [mp.mpc(0) for _ in range(max_order + 1)]
    for j in range(nodes):
        theta = 2 * mp.pi * (j + mp.mpf("0.5")) / nodes
        value = func(center + rho * mp.exp(1j * theta))
        for k in range(max_order + 1):
            sums[k] += value * mp.exp(-1j * k * theta)
    return [mp.factorial(k) * sums[k] / (nodes * rho**k)
            for k in range(max_order + 1)]


def circular00_polylog(a):
    with mp.workdps(mp.mp.dps + 12):
        z = mp.mpc(-1) if a == mp.mpf("0.5") else mp.exp(2j * mp.pi * a)
        ds = contour_derivatives(lambda s: mp.polylog(s, z), 0, 2)
        d1, d2 = ds[1].real, ds[2].real
    c = mp.euler + mp.log(2 * mp.pi)
    return 2 * d2 - 4 * c * d1 - c * c - mp.pi**2 / 4


def reflected00(a):
    c = g0(a)

    def f(x):
        if abs(x) < mp.mpf("1e-45"):
            return mp.polygamma(1, a) + mp.euler * c - c / a
        return (g0(a - x) - c) / x + g0(1 + x) * g0(a - x) - c / (a - x)

    return (
        2 * mp.quad(f, [0, a / 4, a / 2])
        + 2 * c * mp.log(a)
        + mp.quad(lambda x: g0(x) * g0(1 + a - x), [a, (1 + a) / 2, 1])
    )


def strnum(x):
    return mp.nstr(x, 52)


def record(kind, a, lhs, rhs):
    row = dict(kind=kind, a=strnum(a), integral=strnum(lhs), formula=strnum(rhs),
               absolute_error=mp.nstr(abs(lhs - rhs), 7))
    print(json.dumps(row), flush=True)
    return row


def main():
    rows = []
    for a in [mp.mpf(1) / 2, mp.mpf(1) / 3, mp.mpf(1) / 4,
              mp.mpf(1) / 6, mp.sqrt(2) - 1]:
        rows.append(record("circular00", a, circular00(a), circular00_polylog(a)))
        rows.append(record("reflected00", a, reflected00(a), 2 * mp.stieltjes(1, a) + mp.zeta(2)))
    a = mp.mpf(1) / 2
    rhs = 2 * mp.stieltjes(1) - 4 * mp.euler * mp.log(2) - 2 * mp.log(2)**2 - mp.pi**2 / 3
    rows.append(record("circular00_half_rational", a, circular00(a), rhs))
    Path(__file__).with_name("results00.json").write_text(json.dumps(rows, indent=2) + "\n")


if __name__ == "__main__":
    main()
