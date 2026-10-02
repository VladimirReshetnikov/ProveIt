#!/usr/bin/env python3
"""Numerical shifted-Apéry checks, not a proof or an interval certificate.

All imports are local or listed in requirements.txt. No source downloads,
repository checkout, data files or network access are needed at runtime.
"""

import argparse
from fractions import Fraction
import json

import mpmath as mp
import numpy as np
from scipy.fft import dct

from density import critical_shift, density, endpoint, right_endpoint_log_weight


def cosine_coefficients(values):
    """Midpoint DCT coefficients for f(theta) = f0+2 sum fk cos(k theta)."""
    values = np.asarray(values, dtype=float)
    return dct(values, type=2) / (2 * len(values))


def sf(s, M=512, density_dps=40):
    """Compute F(s), f0, endpoint bias, quadratic energy Q, and E.

    Hypergeometric values use density_dps decimal digits. The DCT and the
    final quadrature sums deliberately use float64, as in the reference run.
    Increasing density_dps alone does not make these constants arbitrary
    precision. M is the number of equally spaced angle midpoints.
    """
    if M < 8 or density_dps < 25:
        raise ValueError("Use M >= 8 and density_dps >= 25.")
    with mp.workdps(density_dps):
        slope = Fraction(str(s))
        s = mp.mpf(slope.numerator) / slope.denominator
        if not mp.isfinite(s) or s <= critical_shift():
            raise ValueError("This replay requires s > s* = 3 sqrt(2)/4 - 1.")
        C = endpoint()
        a = (s / (s + 2)) ** 2
        values, weights = [], []
        for j in range(M):
            theta = mp.pi * (mp.mpf(j) + mp.mpf("0.5")) / M
            t = (1 + a) / 2 + (1 - a) * mp.cos(theta) / 2
            values.append(float(mp.log(C * density(C * t) / mp.sqrt(1 - t))))
            weights.append(float((s + 2) * (1 - a) * mp.cos(theta / 2)**2 / (2 * t)))
        values, weights = np.asarray(values), np.asarray(weights)
        coeff = cosine_coefficients(values)
        F = float(np.dot(values, weights) / M)
        Q = float(0.5 * sum(k * coeff[k]**2 for k in range(1, M)))
        f1 = float(right_endpoint_log_weight())
        bias = float(0.25 * (coeff[0] - f1))
        return {
            "s": str(s), "a": str(a), "F": F, "f0": float(coeff[0]),
            "f1": f1, "bias": bias, "Q": Q,
            "E": float(mp.exp(bias + Q)), "M": M,
            "last_coeff": float(coeff[-1]),
        }


def moments(kmax):
    """Return exact integers A_0,...,A_kmax by the Apéry recurrence."""
    if kmax < 0:
        raise ValueError("kmax must be nonnegative.")
    values = [1, 5]
    for k in range(1, kmax):
        numerator = ((34*k**3 + 51*k*k + 27*k + 5) * values[-1]
                     - k**3 * values[-2])
        value, remainder = divmod(numerator, (k + 1)**3)
        if remainder:
            raise ArithmeticError("The Apéry recurrence division was not exact.")
        values.append(value)
    return values[:kmax + 1]


def logdet(N, r, dps):
    """Log det[A_(r+i+j)/C^(r+i+j)] with N rows, not N+1.

    Integer moments are exact; Schur-complement elimination uses mpmath.
    Positive pivots detect some loss of precision but do not certify accuracy.
    """
    if N < 1 or r < 0 or int(N) != N or int(r) != r:
        raise ValueError("N must be a positive integer and r a nonnegative integer.")
    with mp.workdps(dps):
        C = endpoint()
        values = moments(r + 2*N - 2)
        H = [[mp.mpf(values[r+i+j]) / C**(r+i+j)
              for j in range(N)] for i in range(N)]
        answer = mp.mpf(0)
        for k in range(N):
            pivot = H[k][k]
            if pivot <= 0:
                raise ArithmeticError("Nonpositive pivot; increase --dps.")
            answer += mp.log(pivot)
            for i in range(k + 1, N):
                factor = H[i][k] / pivot
                for j in range(i, N):
                    H[j][i] = H[i][j] = H[i][j] - factor * H[k][j]
        return +answer


def selberg(N, r, b=None):
    """Log det[B(r+i+j+1,b+1)], the N-by-N Jacobi moment determinant.

    This gamma product already includes the 1/N! from the Hankel integral.
    It is the reference weight t^r(1-t)^b on [0,1].
    """
    b = mp.mpf("0.5") if b is None else mp.mpf(b)
    return sum(mp.loggamma(j+1) + mp.loggamma(r+j+1)
               + mp.loggamma(b+j+1) - mp.loggamma(r+b+N+j+1)
               for j in range(N))


def evaluate(s="1", M=512, sizes=(20, 40, 80), dps=None, density_dps=40):
    constants = sf(s, M, density_dps)
    checks = []
    # Parse rational shifts exactly so the r=sN requirement is not a float test.
    slope = Fraction(str(s))
    for N in sizes:
        exact_shift = slope * N
        if exact_shift.denominator != 1:
            raise ValueError("Choose N with integral r=sN; this script does not round shifts.")
        r = exact_shift.numerator
        working_dps = max(120, 4*N) if dps is None else dps
        with mp.workdps(working_dps):
            actual = logdet(N, r, working_dps)
            reference = selberg(N, r)
            residual = actual - reference - N * mp.mpf(str(constants["F"]))
            error = residual - mp.mpf(str(constants["bias"] + constants["Q"]))
            checks.append({
                "N": N, "r": r,
                "logratio_minus_NF": mp.nstr(residual, 20),
                "log_relative_error": mp.nstr(error, 20),
                "N_times_error": mp.nstr(N*error, 20),
            })
    return {"status": "numerical, not a proof or interval certificate",
            "constants": constants, "checks": checks}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--M", type=int, default=512)
    parser.add_argument("--N", default="20,40,80", help="comma-separated matrix orders")
    parser.add_argument("--s", default="1", help="a decimal or rational slope; sN must be integral")
    parser.add_argument("--dps", type=int, help="determinant precision; default max(120,4N)")
    parser.add_argument("--density-dps", type=int, default=40)
    args = parser.parse_args()
    print(json.dumps(evaluate(args.s, args.M, tuple(map(int, args.N.split(","))),
                              args.dps, args.density_dps), indent=2))


if __name__ == "__main__":
    main()
