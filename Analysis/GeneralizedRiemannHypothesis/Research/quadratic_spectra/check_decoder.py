#!/usr/bin/env python3
"""Numerical finite-height decoder for the primitive odd quadratic character mod 3.

Run with Python 3, NumPy and SciPy. Optionally pass --spot-check for an
independent mpmath comparison. All zero enumeration and count diagnostics
use floating-point sampling; this program provides no interval certificate.
"""
import argparse
import math
from fractions import Fraction

import numpy as np
from scipy.optimize import brentq
from scipy.special import bernoulli, loggamma


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--spot-check", action="store_true",
                        help="compare four complex values with mpmath")
    args = parser.parse_args()
    q, bound = 3, 5
    h = Fraction(1, 8 * bound)
    r = 2
    while 2**r < 32 * r * math.sqrt(bound) * math.log(
        math.e * q * 16 * r * bound) / math.log(2):
        r += 2
    cutoff = 16 * r * bound

    # L(s) = 3^(-s) [zeta(s,1/3)-zeta(s,2/3)]. Sum the first N terms
    # of each Hurwitz series with the power of 3 already incorporated.
    # Evaluate its tail by Euler--Maclaurin through B_24.
    terms = cutoff + 32
    indices = 3 * np.arange(terms)[:, None] + np.array([1, 2])
    log_nodes = np.log(indices.ravel())
    signs = np.tile([1, -1], terms)
    bern = bernoulli(24)
    coefficients = [bern[2*k] / math.factorial(2*k) for k in range(1, 13)]

    def lvalues(points):
        s = np.atleast_1d(points).astype(complex)
        direct = (np.exp(-s[:, None] * log_nodes[None, :]) * signs).sum(axis=1)
        for residue, sign in [(1, 1), (2, -1)]:
            x = terms + residue / 3
            tail = x / (s - 1) + 0.5
            product = s / x
            for k, coefficient in enumerate(coefficients, start=1):
                tail += coefficient * product
                product = product * ((s + 2*k - 1) / x) * ((s + 2*k) / x)
            direct += sign * np.exp(-s * math.log(3*x)) * tail
        return direct

    def theta(t):
        return loggamma(0.75 + 0.5j*t).imag + t*math.log(3/math.pi)/2

    def hardy(t):
        return (np.exp(1j*theta(t)) * lvalues(0.5 + 1j*t)).real

    # Independent estimate of N_+(T). At sigma=2 the Euler product picks
    # the principal argument: |L(2+iT)-1| <= zeta(2)-1 < 1. Continue that
    # argument horizontally to the critical line. L(1/2)>0 by paired terms.
    line = np.linspace(2, 0.5, 257) + 1j*cutoff
    values = np.concatenate([lvalues(a) for a in np.array_split(line, 5)])
    increments = np.angle(values[1:] / values[:-1])
    continued_arg = np.angle(values[0]) + increments.sum()
    index = (theta(cutoff) + continued_arg)/math.pi
    expected = round(index)
    if abs(index - expected) > 1e-8:
        raise ArithmeticError("Argument count too far from an integer")

    for subdivisions in [10, 20, 40]:
        mesh = np.arange(subdivisions*cutoff + 1) / subdivisions
        vals = np.concatenate([hardy(a) for a in np.array_split(
            mesh, (len(mesh) + 63) // 64)])
        brackets = np.flatnonzero(np.signbit(vals[:-1]) != np.signbit(vals[1:]))
        if len(brackets) == expected:
            break
    else:
        raise ArithmeticError("Sign scan and numerical argument count disagree")
    roots = np.array([brentq(lambda t: hardy(t)[0], mesh[k], mesh[k+1],
                            xtol=3e-12) for k in brackets])

    # If S is the sum of r independent U[0,1] variables then
    # f(0) = (r/(2h)) times the Irwin--Hall density of S at r/2.
    numerator = sum((-1)**k * math.comb(r, k) * (r//2-k)**(r-1)
                    for k in range(r//2 + 1))
    fzero = r * Fraction(numerator, math.factorial(r-1)) / (2*h)
    transform = np.sinc(float(h)*roots / (r*math.pi))**r
    print("Floating-point illustration; zero completeness is not interval-certified.")
    print(f"q={q}  Q={q}  X={bound}  r={r}  h={h}  T={cutoff}")
    print(f"Exact f(0)={fzero}  (approximately {float(fzero):.9f})")
    print(f"Positive sign-change roots={len(roots)}  mesh width=1/{subdivisions}")
    print(f"Horizontal argument count={index:.9f}  "
          f"maximum sampled argument increment={np.max(abs(increments)):.6f}")
    print(f"First and last positive roots: {roots[0]:.10f}, {roots[-1]:.10f}")
    print("n      spectral estimate    rounded    exact")
    for n, p, actual in [(2, 2, -1), (3, 3, 0), (4, 2, 1), (5, 5, -1)]:
        weight = -math.sqrt(n) / (math.log(p)*float(fzero))
        estimate = 2 * weight * np.dot(np.cos(roots*math.log(n)), transform)
        print(f"{n}  {estimate:20.12f}    {round(estimate):7d}  {actual:7d}")
        if round(estimate) != actual:
            raise ArithmeticError(f"Decoder mismatch for n={n}")
    if args.spot_check:
        import mpmath as mp
        mp.mp.dps = 35
        points = np.array([0.5+9j, 0.5+701j, 0.5+1120j, 1.2+1119j])
        reference = np.array([complex(mp.dirichlet(complex(s), [0,1,-1]))
                              for s in points])
        discrepancy = np.max(abs(lvalues(points) - reference))
        print(f"Four independent mpmath comparisons, max absolute L error={discrepancy:.2e}")
        if discrepancy > 1e-9:
            raise ArithmeticError("Euler--Maclaurin comparison failed")


if __name__ == "__main__":
    main()
