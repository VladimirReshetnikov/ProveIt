#!/usr/bin/env python3
"""Exact finite checks for the accompanying theta-descent article.

Requires Python >= 3.9 and SymPy. No network or floating-point mathematics.
These checks do NOT verify infinite support arguments or transcendence proofs.

Run: python verify.py --precision 64 --output verification.json
"""
from __future__ import annotations

import argparse
import json
import platform
import time
from collections import Counter
from math import isqrt
from pathlib import Path
from typing import Dict

import sympy as sp

x = sp.Symbol("x")
PolySeries = Dict[int, sp.Poly]
ZERO = sp.Poly(0, x, domain=sp.QQ)
ONE = sp.Poly(1, x, domain=sp.QQ)


class TruncatedSeries:
    """Polynomial-valued formal q-series, retaining q-exponents below precision."""

    def __init__(self, precision: int):
        if precision < 8:
            raise ValueError("precision must be at least 8")
        self.precision = precision

    def clean(self, a: PolySeries) -> PolySeries:
        return {i: p for i, p in a.items() if 0 <= i < self.precision and not p.is_zero}

    def scalar(self, value) -> PolySeries:
        return self.clean({0: sp.Poly(value, x, domain=sp.QQ)})

    def add(self, a: PolySeries, b: PolySeries) -> PolySeries:
        c = a.copy()
        for i, p in b.items():
            c[i] = c.get(i, ZERO) + p
        return self.clean(c)

    def scale(self, a: PolySeries, scalar) -> PolySeries:
        return self.clean({i: p * scalar for i, p in a.items()})

    def mul(self, a: PolySeries, b: PolySeries) -> PolySeries:
        c: PolySeries = {}
        for i, p in a.items():
            for j, q in b.items():
                if i + j < self.precision:
                    c[i + j] = c.get(i + j, ZERO) + p * q
        return self.clean(c)

    def power(self, a: PolySeries, n: int) -> PolySeries:
        if n < 0:
            raise ValueError("nonnegative powers only")
        out = {0: ONE}
        while n:
            if n & 1:
                out = self.mul(out, a)
            a = self.mul(a, a)
            n >>= 1
        return out

    def derivative(self, a: PolySeries) -> PolySeries:
        return self.clean({i: p.diff() for i, p in a.items()})

    def lambert(self, r: int) -> PolySeries:
        return {
            2 * n: sp.Poly(sum(d**r for d in sp.divisors(n)), x, domain=sp.QQ)
            for n in range(1, (self.precision + 1) // 2)
        }


def chebyshev(maximum: int):
    c = [sp.Poly(2, x, domain=sp.QQ), sp.Poly(x, x, domain=sp.QQ)]
    for n in range(2, maximum + 1):
        c.append(sp.Poly(x, x, domain=sp.QQ) * c[-1] - c[-2])
    return c


def combine(terms):
    """Normalize an exact Laurent polynomial in q, from exponent/coefficient pairs."""
    out = Counter()
    for exponent, coefficient in terms:
        out[exponent] += coefficient
    return {e: c for e, c in out.items() if c}


def leading(terms):
    p = combine(terms)
    if not p:
        return None
    exponent = min(p)
    return exponent, p[exponent]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=64)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.precision < 8 or args.precision > 160:
        parser.error("choose precision between 8 and 160")
    started = time.perf_counter()
    counts = Counter()

    def check(condition, category: str, detail: str = ""):
        if not condition:
            raise AssertionError(f"{category}: {detail}")
        counts[category] += 1

    c = chebyshev(max(42, isqrt(args.precision) + 2))
    u = sp.Symbol("u")
    for n in range(1, 31):
        explicit = sum(
            (-1)**j * sp.Rational(n, n-j) * sp.binomial(n-j, j) * x**(n-2*j)
            for j in range(n//2 + 1)
        )
        check(c[n] == sp.Poly(explicit, x, domain=sp.QQ), "Chebyshev closed coefficients", str(n))
        reciprocal = sp.expand(c[n].as_expr().subs(x, u + 1/u) - u**n - u**(-n))
        check(reciprocal == 0, "Chebyshev reciprocal substitution", str(n))
        for m in range(n + 1):
            if (n-m) % 2:
                predicted = 0
            elif m == 0:
                predicted = 2 * (-1)**(n//2)
            else:
                j = (n-m)//2
                predicted = (-1)**j * sp.Rational(m+2*j, m+j) * sp.binomial(m+j, j)
            check(c[n].nth(m) == predicted, "Taylor coefficient extraction", f"n={n}, m={m}")

    for n in range(-40, 41):
        check(n*n + 2*n == (n+1)**2 - 1, "Theta shift exponents", str(n))

    S = TruncatedSeries(args.precision)
    f = {0: ONE}
    for n in range(1, len(c)):
        if n*n < args.precision:
            f[n*n] = c[n]
    f1 = S.derivative(f)
    f2 = S.derivative(f1)
    h = S.add(
        S.mul(S.scalar(x*x-4), S.add(S.mul(f, f2), S.scale(S.mul(f1, f1), -1))),
        S.mul(S.scalar(x), S.mul(f, f1)),
    )
    j = S.add(S.mul(f, S.derivative(h)), S.scale(S.mul(f1, h), -2))
    const_c = S.add(S.scalar(sp.Rational(1, 12)), S.scale(S.lambert(1), -2))
    g2 = S.add(S.scalar(sp.Rational(1, 12)), S.scale(S.lambert(3), 20))
    g3 = S.add(S.scalar(-sp.Rational(1, 216)), S.scale(S.lambert(5), sp.Rational(7, 3)))
    b = S.add(S.mul(const_c, S.power(f, 2)), S.scale(h, -1))
    residual = S.add(
        S.add(S.mul(S.scalar(x*x-4), S.power(j, 2)), S.scale(S.power(b, 3), -4)),
        S.add(S.mul(S.mul(g2, b), S.power(f, 4)), S.mul(g3, S.power(f, 6))),
    )
    for n in range(args.precision):
        check(residual.get(n, ZERO).is_zero, "Third-order ODE q-coefficients", str(n))

    product = S.scalar(1)
    for m in range(1, args.precision + 1):
        product = S.mul(product, S.add(S.scalar(1), {2*m: -ONE}))
        factor = S.add(S.add(S.scalar(1), {2*m-1: sp.Poly(x, x, domain=sp.QQ)}), {4*m-2: ONE})
        product = S.mul(product, factor)
    difference = S.add(product, S.scale(f, -1))
    for n in range(args.precision):
        check(difference.get(n, ZERO).is_zero, "Jacobi product q-coefficients", str(n))

    Y0, Y1, Y2, Y3, Y4 = sp.symbols("Y0 Y1 Y2 Y3 Y4")
    cc, gg2, gg3 = sp.symbols("c g2 g3")
    H = (x*x-4)*(Y0*Y2-Y1*Y1)+x*Y0*Y1
    DH = sp.diff(H, x) + sum(sp.diff(H, a)*b for a, b in zip((Y0,Y1,Y2,Y3), (Y1,Y2,Y3,Y4)))
    H1 = (x*x-4)*(Y0*Y3-Y1*Y2)+2*x*(Y0*Y2-Y1*Y1)+Y0*Y1+x*(Y1*Y1+Y0*Y2)
    check(sp.expand(DH-H1) == 0, "Exact jet identities", "H derivative")
    J = Y0*H1-2*Y1*H
    B = cc*Y0**2-H
    polynomial = sp.expand((x*x-4)*J*J - 4*B**3 + gg2*B*Y0**4 + gg3*Y0**6)
    check(sp.expand(polynomial.coeff(Y3, 2)-(x*x-4)**3*Y0**4) == 0, "Exact jet identities", "leading coefficient")
    check(sp.Poly(polynomial, Y0,Y1,Y2,Y3).total_degree() == 6, "Exact jet identities", "total degree")
    lam = sp.Symbol("lam")
    check(sp.expand(polynomial.subs({Y0:lam*Y0,Y1:lam*Y1,Y2:lam*Y2,Y3:lam*Y3}) - lam**6*polynomial) == 0,
          "Exact jet identities", "homogeneous")
    A, Bv = sp.symbols("A B")
    curve = (x*x-4)*Bv**2 - (4*(cc-A)**3 - gg2*(cc-A) - gg3)
    Bprime = (-12*(cc-A)**2+gg2-2*x*Bv)/(2*(x*x-4))
    tangent = sp.diff(curve, x)+sp.diff(curve, A)*Bv+sp.diff(curve, Bv)*Bprime
    check(sp.cancel(tangent) == 0, "Exact jet identities", "system preserves curve")
    check(sp.Poly(4*(cc-A)**3-gg2*(cc-A)-gg3, A).degree() == 3,
          "Exact jet identities", "odd cubic degree")

    for m in range(1, 17):
        jm = 2*m-1
        derivative_val, derivative_lc = jm, 1
        ceil_val, ceil_lc = 0, 1
        floor_val, floor_lc = 0, 1
        for k in range(1, m+7):
            jk = 2*k-1
            # Factor 1+q^jk*x+q^(2jk), at root, ceiling, and floor.
            root = leading([(0,1),(jk+jm,-1),(jk-jm,-1),(2*jk,1)])
            if k == m:
                check(root is None, "Root-factor cancellations", str(m))
            else:
                assert root is not None
                derivative_val += root[0]
                derivative_lc *= root[1]
            bv = leading([(0,1),(jk-jm,-1),(2*jk,1)])
            av = leading([(0,1),(jk-jm,-1),(jk,-1),(2*jk,1)])
            assert bv and av
            ceil_val += bv[0]; ceil_lc *= bv[1]
            floor_val += av[0]; floor_lc *= av[1]
        check((derivative_val,derivative_lc) == (-m*m+3*m-1,(-1)**(m-1)),
              "Root and rounding leading terms", f"derivative m={m}")
        check((ceil_val,ceil_lc) == (-m*m+5*m-2,(-1)**(m-1)),
              "Root and rounding leading terms", f"ceiling m={m}")
        check((floor_val,floor_lc) == (-m*m+3*m-1,(-1)**m),
              "Root and rounding leading terms", f"floor m={m}")
        for ev in range(-jm+1, jm+4):
            total_val, total_lc = 0, 1
            for k in range(1, m+7):
                jk = 2*k-1
                terms = [(0,1),(jk+jm,-1),(jk-jm,-1),(jk+ev,1),(2*jk,1)]
                lead = leading(terms)
                assert lead
                total_val += lead[0]; total_lc *= lead[1]
            check((total_val,total_lc) == (-m*m+3*m-1+ev,(-1)**(m-1)),
                  "Finite local-linearization leading terms", f"m={m}, e={ev}")

    for n in range(1, 101):
        # Gamma=Z lex Z, h=(0,1), excluded valuation gamma=(-1,0).
        current = (-n, n*n)
        later = (-(n+1), (n+1)**2)
        check(later < current, "Lexicographic exclusion checks", str(n))

    result = {
        "status": "passed",
        "checks": dict(sorted(counts.items())),
        "total_checks": sum(counts.values()),
        "failures": 0,
        "q_precision_exclusive": args.precision,
        "ode_residual": "zero for every q-coefficient below precision, as an exact polynomial in x",
        "product_residual": "zero for every q-coefficient below precision, as an exact polynomial in x",
        "python": platform.python_version(),
        "sympy": sp.__version__,
        "elapsed_seconds": round(time.perf_counter()-started, 3),
        "not_verified_by_this_program": [
            "strong summability of infinite Hahn supports",
            "minimal differential order and algebraic independence",
            "universal no-order-unit obstruction",
            "infinite zero-set completeness",
            "bibliographic priority or independent correctness review"
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
