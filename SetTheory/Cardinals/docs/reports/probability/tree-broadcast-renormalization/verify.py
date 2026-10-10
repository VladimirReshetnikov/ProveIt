#!/usr/bin/env python3
"""Exact checks for Gaussian renormalization of tree broadcasts.

Only Python's standard library is required.  All reported algebraic checks
use fractions.Fraction; decimal displays are not used in assertions.
Run: python verify.py --output verification.json
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path


def zero(d):
    return [F(0) for _ in range(d + 1)]


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def scale(a, c):
    return [c * x for x in a]


def mul(a, b):
    d = len(a) - 1
    return [sum((a[j] * b[k - j] for j in range(k + 1)), F(0))
            for k in range(d + 1)]


def inv(a):
    d = len(a) - 1
    out = zero(d)
    out[0] = 1 / a[0]
    for k in range(1, d + 1):
        out[k] = -sum((a[j] * out[k - j] for j in range(1, k + 1)), F(0)) / a[0]
    return out


def exp(a):
    assert a[0] == 0
    d = len(a) - 1
    out = zero(d)
    out[0] = F(1)
    for k in range(1, d + 1):
        out[k] = sum((j * a[j] * out[k - j] for j in range(1, k + 1)), F(0)) / k
    return out


def log(a):
    assert a[0] == 1
    d = len(a) - 1
    deriv = [F(k + 1) * a[k + 1] for k in range(d)] + [F(0)]
    quot = mul(deriv, inv(a))
    return [F(0)] + [quot[k - 1] / k for k in range(1, d + 1)]


def critical_sources(q, b):
    """Return atanh(theta*tanh(q))/theta and log(1+c*sinh(q)^2)."""
    d = len(q) - 1
    e = exp(scale(q, 2))
    numerator, denominator = e.copy(), e.copy()
    numerator[0] -= 1
    denominator[0] += 1
    tanh_q = mul(numerator, inv(denominator))
    tanh_sq = mul(tanh_q, tanh_q)
    phi, power = zero(d), tanh_q
    for k in range((d + 1) // 2):
        phi = add(phi, scale(power, F(1, b) ** k / (2 * k + 1)))
        power = mul(power, tanh_sq)
    sinh_sq = scale(add(e, exp(scale(q, -2))), F(1, 4))
    sinh_sq[0] -= F(1, 2)
    term = scale(sinh_sq, F(b - 1, b))
    term[0] += 1
    return phi, log(term)


def critical_step(q, r, b):
    d = len(q) - 1
    phi, lg = critical_sources(q, b)
    q_new, r_new = zero(d), zero(d)
    for k in range(1, d + 1, 2):
        q_new[k] = F(b) ** ((1 - k) // 2) * phi[k]
    for k in range(2, d + 1, 2):
        r_new[k] = F(b) ** (1 - k // 2) * (r[k] + lg[k] / 2)
    r_new[2] -= F(b - 1, 2 * b)
    return q_new, r_new


def critical_fixed(b, d=10):
    q, r = zero(d), zero(d)
    q[1] = F(1)
    for k in range(3, d + 1, 2):
        phi, _ = critical_sources(q, b)
        eig = F(b) ** ((1 - k) // 2)
        q[k] = eig * phi[k] / (1 - eig)
    _, lg = critical_sources(q, b)
    for k in range(4, d + 1, 2):
        eig = F(b) ** (1 - k // 2)
        r[k] = eig * lg[k] / (2 * (1 - eig))
    q_test, r_test = critical_step(q, r, b)
    assert q_test == q and r_test == r
    return add(q, r)


def convolution(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def exact_leaf_pgf(b, theta, n):
    """PGF of number of positive leaves, conditional on root +."""
    p = [F(0), F(1)]
    a = (1 + theta) / 2
    for _ in range(n):
        mixture = [a * x + (1 - a) * y for x, y in zip(p, reversed(p))]
        result = [F(1)]
        for _ in range(b):
            result = convolution(result, mixture)
        p = result
    assert sum(p) == 1 and all(x >= 0 for x in p)
    return p


def run_checks():
    d = 10
    checks = 0
    tables = []
    finite = []
    for b in (2, 3, 4, 5, 9):
        h = critical_fixed(b, d)
        cumulants = [factorial(k) * h[k] for k in range(d + 1)]
        moments = [factorial(k) * x for k, x in enumerate(exp(h))]
        assert cumulants[3] == F(-2, b)
        assert cumulants[4] == F(-2 * (b + 1), b * b)
        assert moments[3] == 1 - F(2, b)
        checks += 3
        tables.append({"b": b,
                       "limiting_cumulants": {str(k): str(cumulants[k]) for k in range(1, d + 1)},
                       "residue_moments": {str(k): str(moments[k]) for k in range(d + 1)}})
        q, r = zero(d), zero(d)
        q[1] = F(1)
        for n in range(21):
            k3, k4 = 6 * q[3], 24 * r[4]
            assert k3 == F(-2, b) * (1 - F(1, b) ** n)
            assert k4 == F(-2 * (b + 1), b * b) * (1 - F(1, b) ** n) + F(8 * (b - 1), b * b) * n * F(1, b) ** n
            checks += 2
            if n in (1, 2, 5, 10, 20):
                finite.append({"b": b, "n": n, "kappa3": str(k3), "kappa4": str(k4)})
            q, r = critical_step(q, r, b)

    independent = []
    for b, root_b, max_n in ((4, 2, 3), (9, 3, 2)):
        theta = F(1, root_b)
        for n in range(max_n + 1):
            p = exact_leaf_pgf(b, theta, n)
            leaves = b ** n
            normalizer = root_b ** n
            raw = [sum((prob * F(2 * k - leaves, normalizer) ** j
                        for k, prob in enumerate(p)), F(0)) for j in range(d + 1)]
            mgf = [raw[j] / factorial(j) for j in range(d + 1)]
            actual_log = log(mgf)
            q, r = zero(d), zero(d)
            q[1] = F(1)
            for _ in range(n):
                q, r = critical_step(q, r, b)
            predicted = add(q, r)
            predicted[2] = F(b - 1, 2 * b) * n
            assert actual_log == predicted
            checks += d + 1
            majority = sum((prob for k, prob in enumerate(p) if 2 * k > leaves), F(0))
            if leaves % 2 == 0:
                majority += p[leaves // 2] / 2
            independent.append({"b": b, "n": n, "leaves": leaves,
                                "all_moments_through": d,
                                "majority_success_exact": str(majority),
                                "majority_success_decimal": float(majority)})
    general = []
    for b, theta, max_n in ((2, F(7, 12), 4), (2, F(1, 2), 4),
                            (2, F(1, 3), 4), (3, F(2, 5), 2),
                            (3, F(1, 2), 2)):
        z, c = theta * theta, 1 - theta * theta
        B = b * theta
        alpha, beta = 1 / B**2, F(b) / B**4
        variance, k3, k4 = F(0), F(0), F(0)
        for n in range(max_n + 1):
            p = exact_leaf_pgf(b, theta, n)
            leaves = b**n
            raw = [sum((prob * (F(2 * k - leaves) / B**n)**j
                        for k, prob in enumerate(p)), F(0)) for j in range(5)]
            actual = log([raw[j] / factorial(j) for j in range(5)])
            assert actual[1] == 1
            assert actual[2] * 2 == variance
            assert actual[3] * 6 == k3
            assert actual[4] * 24 == k4
            checks += 4
            variance = (variance + c) / (b * z)
            k3, k4 = alpha * (k3 - 2 * c), beta * (k4 + 4 * c * k3 - 2 * c * (1 - 3 * z))
        general.append({"b": b, "theta": str(theta), "depths_checked": max_n + 1,
                        "normalization": "X_n=(b*theta)^(-n)*S_n"})

    signs = []
    for b, theta in ((2, F(7, 12)), (2, F(11, 20)), (3, F(2, 5))):
        z, c = theta * theta, 1 - theta * theta
        alpha, beta = 1 / (b * theta)**2, F(b) / (b * theta)**4
        assert beta > 1 > alpha
        C3 = -2 * c / (b*b*z - 1)
        C0 = -2 * c * (1 - 3*z)
        N, D = C0 + 4*c*C3, -4*c*C3
        numerator = N*(beta-alpha) + D*(beta-1)
        explicit = -2*c*alpha*(1 + 3*(b-1)*z - b*z*z)/(b*z)
        assert numerator == explicit
        assert numerator < 0
        checks += 2
        signs.append({"b": b, "theta": str(theta), "initial_fourth_forcing": str(C0),
                      "negative_amplitude_numerator": str(numerator)})
    return {"status": "PASS", "exact_scalar_checks": checks,
            "arithmetic": "fractions.Fraction (all assertions exact)",
            "max_series_order": d, "fixed_residues": tables,
            "finite_cumulants": finite, "independent_pgf_checks": independent,
            "general_parameter_pgf_checks": general, "subthreshold_sign_checks": signs,
            "scope": "Algebraic identities and finite distributions only; analytic convergence is proved in article.tex."}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="verification.json")
    args = parser.parse_args()
    report = run_checks()
    Path(args.output).write_text(json.dumps(report, indent=2) + "\n")
    print(f"{report['status']}: {report['exact_scalar_checks']} exact scalar checks; output {args.output}")
    for row in report["fixed_residues"]:
        print("b=", row["b"], "kappa3..6=", [row["limiting_cumulants"][str(k)] for k in range(3, 7)],
              "A3,A5=", [row["residue_moments"][str(k)] for k in (3, 5)])


if __name__ == "__main__":
    main()
