#!/usr/bin/env python3
"""Exact finite checks accompanying Singular Curves over Omnific Integers.

These tests do not formalize infinite Hahn series, scheme theory, or the
universal mathematical theorems. Python 3.10+ and SymPy are required.
Run: python verify.py --output verification.json
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb, factorial, gcd
from pathlib import Path
import json
import platform
import random
import sys
import time

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required: python -m pip install sympy") from exc

COUNTS: Counter[str] = Counter()


def check(condition: bool, group: str, detail: str = "") -> None:
    if not condition:
        raise AssertionError(f"{group}: {detail}")
    COUNTS[group] += 1


def mul_truncated(a: list[Fraction], b: list[Fraction], n: int) -> list[Fraction]:
    out = [Fraction(0) for _ in range(n + 1)]
    for i, ai in enumerate(a[: n + 1]):
        for j, bj in enumerate(b[: n + 1 - i]):
            out[i + j] += ai * bj
    return out


def power_truncated(a: list[Fraction], exponent: int, n: int) -> list[Fraction]:
    out = [Fraction(1)] + [Fraction(0)] * n
    for _ in range(exponent):
        out = mul_truncated(out, a, n)
    return out


def check_taylor(rng: random.Random) -> None:
    # Arbitrary rational jets: E(d b^j)=E(d)E(b)^j.
    # The coefficient sum must be d_0^2 b_1^n, for all tested jets.
    for n in range(11):
        for case in range(24):
            d = [Fraction(rng.randint(-5, 5), rng.randint(1, 5))
                 / factorial(j) for j in range(n + 2)]
            b = [Fraction(rng.randint(-5, 5), rng.randint(1, 5))
                 / factorial(j) for j in range(n + 2)]
            coefficient = Fraction(0)
            for j in range(n + 1):
                e_dbj = mul_truncated(d, power_truncated(b, j, n), n)
                coefficient += ((-1) ** (n-j) * comb(n, j)
                                * d[0] * b[0] ** (n-j) * e_dbj[n])
            expected = d[0] ** 2 * b[1] ** n
            check(coefficient == expected, "rational_jet_identity",
                  f"n={n}, case={case}")
    x = sp.symbols("x")
    d, b = x*x+2*x+3, x*x-x+2
    for n in range(8):
        rhs = sum((-1)**(n-j) * sp.binomial(n, j) * d*b**(n-j)
                  * sp.diff(d*b**j, x, n) for j in range(n+1)) / sp.factorial(n)
        check(sp.expand(rhs - d*d*sp.diff(b, x)**n) == 0,
              "symbolic_taylor_identity", f"n={n}")


# Sparse, finite-support Hahn arithmetic over the rational exponent group.
Series = dict[Fraction, Fraction]


def clean(f: Series) -> Series:
    return {e: a for e, a in f.items() if a}


def add(f: Series, g: Series) -> Series:
    out = dict(f)
    for e, a in g.items():
        out[e] = out.get(e, Fraction(0)) + a
    return clean(out)


def multiply(f: Series, g: Series) -> Series:
    out: Series = {}
    for e, a in f.items():
        for h, b in g.items():
            out[e+h] = out.get(e+h, Fraction(0)) + a*b
    return clean(out)


def derive(f: Series) -> Series:
    return clean({e: e*a for e, a in f.items()})


def random_series(rng: random.Random) -> Series:
    out: Series = {}
    for _ in range(rng.randint(1, 8)):
        exponent = -Fraction(rng.randint(0, 20), rng.randint(1, 7))
        coefficient = Fraction(rng.randint(-5, 5), rng.randint(1, 5))
        out[exponent] = out.get(exponent, Fraction(0)) + coefficient
    return clean(out)


def check_hahn(rng: random.Random) -> None:
    for _ in range(150):
        f, g = random_series(rng), random_series(rng)
        fg = multiply(f, g)
        check(derive(fg) == add(multiply(derive(f), g), multiply(f, derive(g))),
              "finite_hahn_leibniz")
        check(fg.get(Fraction(0), 0) == f.get(Fraction(0), 0)*g.get(Fraction(0), 0),
              "finite_hahn_constant_term")
        if f and g:
            check(min(fg) == min(f)+min(g), "finite_hahn_valuation")
        df = f
        for _ in range(6):
            df = derive(df)
            check(set(df).issubset(f), "finite_hahn_iterated_support")
        if f and min(f) < 0:
            check(min(derive(f)) == min(f), "finite_hahn_leading_probe")
    # Explicit lexicographic rank-two checks: H=(1,0), e=(0,1).
    H, e = (1, 0), (0, 1)
    for n in range(1, 101):
        check((0, n) < H, "rank_two_high_scale")
        check((-1, 2*n-1) < (0, 0), "rank_two_shifted_root_support")


def check_superelliptic() -> None:
    # Complete enumeration of nonzero multiplicity residues at 1--3 roots,
    # for m=2,...,20. Zero residues add no ramification and do not affect
    # gcd(m,degree), so are separately checked below.
    configs = 0
    for m in range(2, 21):
        for r in range(1, 4):
            for exponents in product(range(1, m), repeat=r):
                if gcd(m, *exponents) != 1:
                    continue
                configs += 1
                deficit = sum(m-gcd(m, e) for e in exponents)
                r_inf = gcd(m, sum(exponents))
                two_g = 2-m-r_inf+deficit
                geometric = two_g == 0 and r_inf == 1
                multiplicity = r == 1 and gcd(m, exponents[0]) == 1
                check(two_g >= 0 and two_g % 2 == 0,
                      "superelliptic_genus_integrality")
                check(geometric == multiplicity, "superelliptic_equivalence")
                check(gcd(m, sum(exponents)+3*m) == r_inf,
                      "superelliptic_full_power_invariance")
    x, T = sp.symbols("x T")
    Q = x*x-3*x+2
    for m in range(2, 9):
        for e in range(1, m):
            if gcd(m, e) != 1:
                continue
            X = 3+T**m
            Y = 2*Q.subs(x, X)*T**e
            error = Y**m - 2**m * Q.subs(x, X)**m * (X-3)**e
            check(sp.expand(error) == 0, "superelliptic_normalization_identity")
    check(configs > 0, "enumeration_nonempty")


def check_examples() -> None:
    x, y, z, T, dx = sp.symbols("x y z T dx")
    f = x**3-x+1
    U = (18*x+27)/23
    V = (-6*x*x-9*x+4)/23
    check(sp.expand(U*f + V*sp.diff(f, x)) == 1, "elliptic_bezout")
    check(sp.discriminant(f, x) == -23, "elliptic_discriminant")
    check(sp.rem((x*y)**2-x*x*f, y*y-f, y) == 0,
          "pinched_normalization_identity")
    for j in range(15):
        representative = x*f**(j//2) if j % 2 == 0 else z*f**(j//2)
        check(not representative.has(y), "conductor_representative")
        check(sp.rem(x*y**j-representative.subs(z, x*y), y*y-f, y) == 0,
              "conductor_membership_identity")
    # Clear 2y before reducing the differential identity modulo y^2=f.
    cleared_error = U*y*y*dx + V*sp.diff(f, x)*dx - dx
    check(sp.rem(cleared_error, y*y-f, y) == 0,
          "elliptic_differential_identity")
    check(3*(-2)+7 == 1, "seventh_order_valuation_certificate")
    # Rational node, cusp, and real negative-coefficient one-branch families.
    check(sp.expand((T*(T*T-1))**2 - (T*T-1)**2*((T*T-1)+1)) == 0,
          "node_parametrization")
    check(sp.expand((T**3)**2-(T**2)**3) == 0, "cusp_parametrization")
    for c in [-3, -1, 1, 2, 5]:
        X = 2+c*T*T
        Y = c*(X-1)*T
        check(sp.expand(Y*Y-c*(X-1)**2*(X-2)) == 0,
              "real_signed_parametrization")
    check(sp.expand((T*(T*T+1))**2-(T*T+1)**2*((T*T+1)-1)) == 0,
          "acnode_parametrization")
    check((T*T+1).subs(T, sp.I) == 0 and
          (T*(T*T+1)).subs(T, sp.I) == 0, "acnode_complex_preimage")


def check_jet_bound() -> None:
    for m in range(1, 9):
        for delta in range(21):
            for r in range(11):
                n = ((2*m+1)*delta)//(r+1)+1
                check(n*(r+1)-(2*m+1)*delta > 0,
                      "jet_bound_positive")
                check((n-1)*(r+1)-(2*m+1)*delta <= 0,
                      "jet_bound_minimal_for_given_parameters")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="Write a JSON report at this path (explicit opt-in).")
    args = parser.parse_args()
    started = time.monotonic()
    rng = random.Random(20260923)
    check_taylor(rng)
    check_hahn(rng)
    check_superelliptic()
    check_examples()
    check_jet_bound()
    report = {
        "status": "PASS",
        "scope": "Exact finite regression checks; not a formal proof of the paper.",
        "python": platform.python_version(),
        "sympy": sp.__version__,
        "seed": 20260923,
        "assertions": sum(COUNTS.values()),
        "groups": dict(sorted(COUNTS.items())),
        "elapsed_seconds": round(time.monotonic()-started, 3),
        "not_checked": [
            "arbitrary infinite Hahn series or their summability",
            "normalization of an arbitrary affine curve",
            "Riemann-Roch or Riemann-Hurwitz",
            "the universal quantified conclusions of the article",
            "historical novelty or independent peer review",
        ],
    }
    text = json.dumps(report, indent=2)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text+"\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, OSError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
