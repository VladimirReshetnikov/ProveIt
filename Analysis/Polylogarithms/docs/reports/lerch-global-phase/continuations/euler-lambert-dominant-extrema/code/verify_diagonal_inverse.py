#!/usr/bin/env python3
"""Replay finite checks for the diagonal inverse theorem.

The proofs are analytic. Exact checks below use only the standard library.
The optional --numeric section uses mpmath and is explicitly diagnostic;
it does not certify global analytic continuation or an asymptotic error bound.

Usage:
    python verify_diagonal_inverse.py --output diagonal_exact.json
    python verify_diagonal_inverse.py --numeric --output diagonal_checks.json
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
import json
import math
from pathlib import Path
import platform


def add(a, b):
    c = [Q(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] += x
    for i, x in enumerate(b):
        c[i] += x
    return c


def multiply(a, b):
    c = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return c


def scale(a, c):
    return [c * x for x in a]


def stirling_polynomials(max_n):
    """p_n(L)=A^n v_n(A), exact coefficients in increasing powers of L."""
    row = [1]
    result = [[Q(0)]]
    for n in range(1, max_n + 1):
        new = [0] * (n + 1)
        for k in range(n + 1):
            new[k] = ((row[k - 1] if k else 0)
                      + (n - 1) * (row[k] if k < n else 0))
        row = new
        result.append([Q(0)] + [Q((-1) ** j * row[n - j + 1],
                                        math.factorial(j))
                                     for j in range(1, n + 1)])
    return result


def recurrence_polynomials(max_n):
    # (n+1)p_(n+1)=(n+1-nL)p_n+(n/2) sum_(j=1)^(n-1) p_j p_(n-j).
    p = [[Q(0)], [Q(0), Q(-1)]]
    for n in range(1, max_n):
        rhs = multiply([Q(n + 1), Q(-n)], p[n])
        for j in range(1, n):
            rhs = add(rhs, scale(multiply(p[j], p[n - j]), Q(n, 2)))
        p.append(scale(rhs, Q(1, n + 1)))
    return p


def interval_product(a, b):
    vals = [x * y for x in a for y in b]
    return min(vals), max(vals)


def interval_horner(poly, x):
    y = Q(0), Q(0)
    for c in reversed(poly):
        low, high = interval_product(y, x)
        y = low + c, high + c
    return y


def log2_interval(terms=45):
    lo = sum((Q(2, (2 * j + 1) * 3 ** (2 * j + 1))
              for j in range(terms)), Q(0))
    tail = Q(2, (2 * terms + 1) * 3 ** (2 * terms + 1)) / Q(8, 9)
    return lo, lo + tail


def frac(x):
    return f"{x.numerator}/{x.denominator}"


def exact_checks(max_n=35):
    direct = stirling_polynomials(max_n)
    recursive = recurrence_polynomials(max_n)
    assert direct == recursive
    interval = log2_interval()
    signs = {}
    enclosures = {}
    for n in range(1, max_n + 1):
        a, b = interval_horner(direct[n], interval)
        a, b = a / 2 ** n, b / 2 ** n
        assert a > 0 or b < 0, (n, a, b)
        signs[str(n)] = 1 if a > 0 else -1
        if n <= 12:
            enclosures[str(n)] = [frac(a), frac(b)]
    assert signs["4"] == 1
    return {
        "status": "passed",
        "arithmetic": "exact fractions, no floating point",
        "independent_polynomial_representations_checked_through": max_n,
        "polynomial_recurrence":
            "(n+1)p[n+1]=(n+1-nL)p[n]+(n/2)sum(p[j]p[n-j],j=1..n-1)",
        "log2_enclosure": [frac(x) for x in interval],
        "certified_A2_signs": signs,
        "first_twelve_A2_enclosures": enclosures,
        "first_six_p_polynomials":
            [[frac(c) for c in direct[n]] for n in range(1, 7)],
    }


def numerical_checks(max_n=240, dps=360):
    import mpmath as mp

    mp.mp.dps = dps
    polys = stirling_polynomials(max_n)

    def real(x):
        return mp.nstr(x, 35)

    def complex_value(x):
        return {"real": real(mp.re(x)), "imag": real(mp.im(x))}

    def parameters(A):
        low, high = mp.mpf(0), mp.pi
        for _ in range(int(dps * 3.5)):
            theta = (low + high) / 2
            Ltheta = 1 - theta * mp.cot(theta) + mp.log(theta / mp.sin(theta))
            if Ltheta < mp.log(A):
                low = theta
            else:
                high = theta
        theta = (low + high) / 2
        a = 1 - theta * mp.cot(theta)
        u = mp.mpc(a, theta)
        chi = mp.sqrt(-2 * u)
        assert mp.re(chi) > 0 and mp.im(chi) < 0
        return theta, a, u, mp.exp(u), mp.exp(a), chi

    output = {}
    for Atext in ["1.1", "2", "4", "10"]:
        A = mp.mpf(Atext)
        L = mp.log(A)
        theta, a, u, tau, radius, chi = parameters(A)
        chi1 = chi * (-mp.mpf(3) / 8 + u / 12 + 3 / (8 * u))
        v = [mp.mpf(0)]
        for n in range(1, max_n + 1):
            pval = mp.polyval([mp.mpf(q.numerator) / q.denominator
                              for q in reversed(polys[n])], L)
            v.append(pval / A ** n)

        # Independent numeric coefficient recurrence.
        rec = [mp.mpf(0), -L / A]
        for n in range(1, max_n):
            conv = mp.fsum(rec[j] * rec[n-j] for j in range(1, n))
            rec.append(((n + 1 - n * L) * rec[n] + mp.mpf(n) * conv / 2)
                       / (A * (n + 1)))
        max_rel = max(abs(v[n] - rec[n]) / max(abs(v[n]), mp.mpf("1e-1000"))
                      for n in range(1, max_n + 1))
        assert max_rel < mp.mpf("1e-150"), (Atext, max_rel)

        samples = []
        max_error0 = mp.mpf(0)
        max_error1 = mp.mpf(0)
        for n in range(40, max_n + 1):
            normalized = mp.sqrt(mp.pi) * radius ** n * mp.mpf(n) ** mp.mpf("1.5") * v[n]
            model0 = mp.re(chi * mp.exp(-1j * n * theta))
            model1 = mp.re((chi + chi1 / n) * mp.exp(-1j * n * theta))
            err0, err1 = abs(normalized - model0), abs(normalized - model1)
            max_error0 = max(max_error0, n * err0)
            max_error1 = max(max_error1, n * n * err1)
            if n in [40, 80, 160, 240]:
                samples.append({"n": n, "velocity": real(v[n]),
                                "normalized_error_leading": real(err0),
                                "normalized_error_corrected": real(err1)})

        # Endpoint finite-part sum, with expected residual O(N^(-1/2)).
        critical_samples = []
        critical_sum = mp.mpc(0)
        derivative_sum = mp.mpc(0)
        for n in range(1, max_n + 1):
            term = v[n] * tau ** n
            critical_sum += term
            derivative_sum += n * term
            if n in [40, 80, 160, 240]:
                boundary_residual = critical_sum - (L - u)
                finite_part_residual = derivative_sum - chi * mp.sqrt(n / mp.pi) - (u / 3 - 1)
                critical_samples.append({
                    "N": n,
                    "boundary_residual_times_sqrtN": complex_value(boundary_residual * mp.sqrt(n)),
                    "finite_part_residual_times_sqrtN": complex_value(finite_part_residual * mp.sqrt(n)),
                })

        # Boundary factorization check at separate horizontal points.
        barrier_error = mp.mpf(0)
        for x in [mp.mpf(0), a / 2, a, 2 * a, a + 1, a + 3]:
            h = x - a
            lhs = abs(mp.exp(x + 1j * theta) - A) ** 2 - radius ** 2 * (x*x + theta*theta)
            rhs = radius ** 2 * (mp.exp(h) - 1 - h) * (mp.exp(h) + 1 + h - 2 * (1-a))
            barrier_error = max(barrier_error, abs(lhs - rhs) / max(1, abs(lhs), abs(rhs)))

        output[Atext] = {
            "theta": real(theta), "a": real(a), "radius": real(radius),
            "critical_u": complex_value(u), "critical_t": complex_value(tau),
            "chi": complex_value(chi), "chi1": complex_value(chi1),
            "late_sign_block_length": int(mp.floor(mp.pi / theta)) + 2,
            "coefficient_recurrence_max_relative_difference": real(max_rel),
            "boundary_factorization_max_relative_residual": real(barrier_error),
            "sample_asymptotics": samples,
            "max_n_times_leading_normalized_error": real(max_error0),
            "max_n_squared_times_corrected_normalized_error": real(max_error1),
            "critical_sums": critical_samples,
        }

    return {"status": "diagnostic_only", "mpmath_version": mp.__version__,
            "decimal_precision": dps, "maximum_index": max_n,
            "note": "No continuation or asymptotic bound is certified by these finite computations.",
            "parameters": output}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--numeric", action="store_true")
    parser.add_argument("--output", type=Path, default=Path("diagonal_exact.json"))
    args = parser.parse_args()
    report = {"python": platform.python_version(), "exact": exact_checks()}
    if args.numeric:
        report["numerical"] = numerical_checks()
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Exact polynomial and interval checks passed; wrote {args.output}")
    if args.numeric:
        print("Numerical coefficient, barrier, asymptotic, and boundary diagnostics completed.")


if __name__ == "__main__":
    main()
