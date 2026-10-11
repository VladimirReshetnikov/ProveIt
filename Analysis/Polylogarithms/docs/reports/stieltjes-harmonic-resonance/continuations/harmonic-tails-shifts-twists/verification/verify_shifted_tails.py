#!/usr/bin/env python3
"""Exact algebra and independent asymptotic diagnostics for shifted tail identities.

The proof is in shifted_tail_section.tex. Numerical checks are diagnostics,
not certified error enclosures. Run with Python 3, sympy, and mpmath.
"""
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path

import mpmath as mp
import sympy as sp

V = sp.Symbol("v")
X = sp.Symbol("x")
mp.mp.dps = 85


def rat(value):
    value = sp.Rational(value)
    return mp.mpf(int(value.p)) / int(value.q)


def zsymbol(s):
    return sp.Symbol("Z_%s" % ("m%d" % -s if s < 0 else s))


def l_exact(s, m, v):
    return (
        sum(
            sp.binomial(m + 1, h) * sp.bernoulli(h) * zsymbol(s - m - 1 + h)
            for h in range(0, m + 2, 2)
        )
        - sp.bernoulli(m + 1, v) * zsymbol(s)
    ) / (m + 1)


def k_exact(p, q, d, v):
    return (
        l_exact(p, d - q, v)
        + l_exact(q, d - p, v)
        - (v - 1) ** d * zsymbol(p) * zsymbol(q)
    )


def check_exact_telescopers():
    rows = []
    for p in range(2, 9):
        for q in range(p, 9):
            for d in range(q, q + 6):
                lhs = k_exact(p, q, d, V)
                shifted = k_exact(p, q, d, V + 1)
                replacements = {
                    zsymbol(s): zsymbol(s) - V ** (-s)
                    for s in range(p + q - d - 1, q + 1)
                }
                shifted = shifted.subs(replacements, simultaneous=True)
                target = (V**d - (V - 1) ** d) * zsymbol(p) * zsymbol(q)
                residual = sp.cancel(sp.expand(lhs - shifted - target))
                assert residual == 0, (p, q, d, residual)
                rows.append([p, q, d])
    return rows


def check_exact_transforms():
    rows = []
    for j in range(21):
        rhs = sum(
            sp.binomial(2 * j + 1, 2 * r)
            * sp.Rational(1, 2) ** (2 * (j - r))
            * sp.bernoulli(2 * r + 1, V + sp.Rational(1, 2))
            / (2 * r + 1)
            for r in range(j + 1)
        )
        assert sp.expand(rhs - V ** (2 * j + 1)) == 0
        rows.append(j)
    # Finite rational tail arrays check the lower endpoint and inclusive cutoffs.
    finite_rows = []
    for v in [sp.Rational(3, 4), sp.Rational(3, 2), sp.Rational(7, 3)]:
        p, q, nmax, stop = 2, 4, 7, 23
        tail = {
            s: [sum((v + k) ** (-s) for k in range(n, stop)) for n in range(nmax + 1)]
            for s in [p, q]
        }
        y = nmax + v - 1
        for r in range(7):
            direct = sum(
                (n + v - sp.Rational(1, 2)) ** (2 * r) * tail[p][n] * tail[q][n]
                for n in range(nmax)
            )
            transformed = 0
            for j in range(r + 1):
                d = 2 * j + 1
                e = y**d * tail[p][nmax] * tail[q][nmax]
                e += sum(
                    (k + v) ** (d - p) * tail[q][k + 1]
                    + (k + v) ** (d - q) * tail[p][k + 1]
                    + (k + v) ** (d - p - q)
                    for k in range(nmax)
                )
                transformed += (
                    sp.binomial(2 * r, 2 * j)
                    * sp.bernoulli(2 * r - 2 * j, sp.Rational(1, 2))
                    * e
                    / d
                )
            transformed -= (
                sp.bernoulli(2 * r + 1, v - sp.Rational(1, 2))
                / (2 * r + 1)
                * tail[p][0]
                * tail[q][0]
            )
            assert direct == transformed
            finite_rows.append([str(v), r])
    return {"inverse_polynomial_rows": rows, "finite_endpoint_rows": finite_rows}


def check_derivative_coefficients():
    h = sp.Symbol("h")
    rows = []
    for k in range(2, 25):
        t = sum((-1) ** j * (j + 1) * zsymbol(j + 2) * h**j for j in range(k))
        coefficient = sp.expand(-(h + h**2) * t - h**3 * t**2).coeff(h, k)
        target = (-1) ** k * (
            k * zsymbol(k + 1)
            - (k - 1) * zsymbol(k)
            + sum((a - 1) * (k - a) * zsymbol(a) * zsymbol(k + 1 - a) for a in range(2, k))
        )
        assert sp.expand(coefficient - target) == 0
        rows.append(k)
    return rows


def zvalue(s, v):
    return -mp.digamma(v) if s == 1 else mp.zeta(s, v)


def l_value(s, m, v):
    terms = [rat(sp.binomial(m + 1, h) * sp.bernoulli(h)) * zvalue(s - m - 1 + h, v)
             for h in range(0, m + 2, 2)]
    poly = sp.Poly(sp.bernoulli(m + 1, V), V)
    bval = mp.fsum(rat(c) * v**e[0] for e, c in poly.terms())
    return (mp.fsum(terms) - bval * mp.zeta(s, v)) / (m + 1)


def k_value(p, q, d, v):
    return l_value(p, d - q, v) + l_value(q, d - p, v) - (v - 1) ** d * mp.zeta(p, v) * mp.zeta(q, v)


def centered_product_coefficients(p, q, hmax):
    series = {}
    for s in [p, q]:
        series[s] = [sp.Rational(1, s - 1)] + [
            sp.bernoulli(2 * h, sp.Rational(1, 2)) * sp.rf(s, 2 * h - 1) / sp.factorial(2 * h)
            for h in range(1, hmax + 1)
        ]
    return [sum(series[p][j] * series[q][h - j] for j in range(h + 1)) for h in range(hmax + 1)]


def summand_coefficients(p, q, polynomial, hmax=29):
    product = centered_product_coefficients(p, q, hmax)
    coeffs = defaultdict(lambda: sp.S.Zero)
    for (degree,), coefficient in sp.Poly(polynomial, X).terms():
        for h, value in enumerate(product):
            coeffs[degree + 2 - p - q - 2 * h] += coefficient * value
    # Different polynomial degrees produce a staggered final order. Retain only
    # the common fully determined part of the expansion.
    cutoff = sp.degree(polynomial, X) + 2 - p - q - 2 * hmax
    return {int(e): sp.factor(c) for e, c in coeffs.items() if e >= cutoff and c != 0}


def accelerated_sum(p, q, polynomial, v, nmax=96, derivative=0):
    alpha = v - mp.mpf("0.5")
    coeffs = summand_coefficients(p, q, polynomial)
    pfun = sp.lambdify(X, polynomial, "mpmath")
    pd = sp.lambdify(X, sp.diff(polynomial, X), "mpmath")
    result = mp.mpf("0")
    for n in range(nmax):
        x, z = n + alpha, n + v
        ap, aq = mp.zeta(p, z), mp.zeta(q, z)
        if derivative == 0:
            term = pfun(x) * ap * aq
            subtraction = mp.fsum(rat(c) * x**e for e, c in coeffs.items() if e >= -1)
        elif derivative == 1:
            term = pd(x) * ap * aq - pfun(x) * (p * mp.zeta(p + 1, z) * aq + q * ap * mp.zeta(q + 1, z))
            subtraction = mp.fsum(rat(c) * e * x ** (e - 1) for e, c in coeffs.items() if e >= -1)
        else:
            raise ValueError(derivative)
        result += term - subtraction
    result += mp.fsum(
        rat(c) * mp.zeta(-e, nmax + alpha) if derivative == 0
        else rat(c) * e * mp.zeta(1 - e, nmax + alpha)
        for e, c in coeffs.items() if e < -1
    )
    return result, coeffs


def double_hurwitz(p, w, v, nmax=96, hmax=29):
    out = mp.fsum((n + v) ** (-w) * mp.zeta(p, n + v + 1) for n in range(nmax))
    t = nmax + v
    out += mp.zeta(p + w - 1, t) / (p - 1) - mp.zeta(p + w, t) / 2
    out += mp.fsum(
        rat(sp.bernoulli(2 * h) * sp.rf(p, 2 * h - 1) / sp.factorial(2 * h))
        * mp.zeta(p + w + 2 * h - 1, t)
        for h in range(1, hmax + 1)
    )
    return out


def c_value(p, q, d, v):
    if d < p:
        return double_hurwitz(p, q - d, v) + double_hurwitz(q, p - d, v) + mp.zeta(p + q - d, v)
    if d < q:
        return double_hurwitz(p, q - d, v) + mp.zeta(p + q - d, v) / 2 + l_value(q, d - p, v)
    return l_value(p, d - q, v) + l_value(q, d - p, v)


def check_numerics():
    rows = []
    gate = mp.mpf("1e-45")
    def record(name, lhs, rhs):
        error = abs(lhs - rhs)
        assert error < gate, (name, mp.nstr(error, 8))
        rows.append({"name": name, "lhs": mp.nstr(lhs, 60), "rhs": mp.nstr(rhs, 60), "absolute_residual": mp.nstr(error, 8)})

    for p, q, d, vs in [
        (2, 2, 3, "0.75"), (2, 2, 3, "1.5"), (2, 4, 5, "1.5"),
        (4, 4, 5, "0.75"), (4, 6, 7, "1.25"), (4, 6, 11, "1.25"),
        (2, 8, 13, "1.5"), (6, 8, 17, "0.75")
    ]:
        v = mp.mpf(vs)
        poly = sp.expand((X + sp.Rational(1, 2)) ** d - (X - sp.Rational(1, 2)) ** d)
        lhs, coeffs = accelerated_sum(p, q, poly, v)
        correction = mp.fsum(rat(c) * mp.zeta(-e, v - mp.mpf("0.5")) for e, c in coeffs.items() if e >= 0)
        record(f"ordinary p={p} q={q} d={d} v={vs}", lhs, k_value(p, q, d, v) - correction)

    for p, q, vs in [(2, 2, "0.75"), (2, 4, "1.5"), (4, 6, "1.25")]:
        v = mp.mpf(vs)
        cvals = [c_value(p, q, 2 * j + 1, v) for j in range(7)]
        for r in range(7):
            lhs, coeffs = accelerated_sum(p, q, X ** (2 * r), v)
            lhs += mp.fsum(rat(c) * mp.zeta(-e, v - mp.mpf("0.5")) for e, c in coeffs.items() if e >= 0)
            lhs -= mp.zeta(-2 * r, v - mp.mpf("0.5")) * mp.zeta(p, v) * mp.zeta(q, v)
            rhs = mp.fsum(rat(sp.binomial(2 * r, 2 * j) * sp.bernoulli(2 * r - 2 * j, sp.Rational(1, 2)) / (2 * j + 1)) * cvals[j] for j in range(r + 1))
            record(f"moment p={p} q={q} r={r} v={vs}", lhs, rhs)

    v = mp.mpf("1.5")
    lhs, _ = accelerated_sum(2, 2, 3 * X**2 + sp.Rational(1, 4), v)
    record("half lattice trigamma square", lhs, mp.mpf("1.5") + mp.pi**2 / 8 - mp.pi**4 / 32)
    for vs in ["0.75", "1", "1.5"]:
        v = mp.mpf(vs)
        lhs, _ = accelerated_sum(2, 2, 3 * X**2 + sp.Rational(1, 4), v, derivative=1)
        t, u, a = mp.polygamma(1, v), mp.polygamma(2, v), v - 1
        rhs = 2 + (1 - 2 * v) * t + v * (1 - v) * u - 3 * a**2 * t**2 - 2 * a**3 * t * u
        record(f"derivative v={vs}", lhs, rhs)
        lhs, _ = accelerated_sum(2, 2, 2 * X, v)
        rhs = 3 - 2 * mp.digamma(v) + 2 * mp.digamma(v - mp.mpf("0.5")) + (1 - 2 * v) * t - a**2 * t**2
        record(f"resonant ordinary v={vs}", lhs, rhs)
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=None)
    args = parser.parse_args()
    result = {
        "scope": "Exact rational algebra plus independent numerical asymptotic diagnostics; no certified floating-point enclosures.",
        "exact_telescopers": check_exact_telescopers(),
        "exact_transforms": check_exact_transforms(),
        "derivative_coefficient_rows": check_derivative_coefficients(),
        "numerical_precision_digits": mp.mp.dps,
        "numerical_gate": "1e-45",
        "numerical_rows": check_numerics(),
    }
    out = Path(args.output) if args.output else Path(__file__).with_name("shifted_tail_results.json")
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"exact_telescopers": len(result["exact_telescopers"]),
                      "exact_inverse_transforms": len(result["exact_transforms"]["inverse_polynomial_rows"]),
                      "exact_finite_endpoint_rows": len(result["exact_transforms"]["finite_endpoint_rows"]),
                      "exact_derivative_coefficients": len(result["derivative_coefficient_rows"]),
                      "numerical_rows": len(result["numerical_rows"]),
                      "largest_numerical_residual": max((r["absolute_residual"] for r in result["numerical_rows"]), key=mp.mpf),
                      "output": str(out)}, indent=2))


if __name__ == "__main__":
    main()
