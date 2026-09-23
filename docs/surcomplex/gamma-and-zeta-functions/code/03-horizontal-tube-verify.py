#!/usr/bin/env python3
"""Exact finite checks accompanying the Gamma--zeta article.

These are coefficient and finite-arithmetic checks, NOT a verification of
surreal summability, proper-class theorems, or algebraic independence.
Requires Python >= 3.10 and SymPy 1.14.0. No network access is used.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
import json
from pathlib import Path
import platform
import sys
import time
from typing import Any

import sympy as sp


def bernoulli(n: int) -> sp.Expr:
    """The convention B_1 = -1/2 (explicitly use the polynomial at zero)."""
    return sp.bernoulli(n, 0)


def choose(alpha: sp.Expr, k: int) -> sp.Expr:
    if k < 0:
        return sp.S.Zero
    return sp.prod(alpha - j for j in range(k)) / sp.factorial(k)


class Checks:
    def __init__(self) -> None:
        self.counts: Counter[str] = Counter()
        self.failures: list[dict[str, str]] = []

    def equal(self, category: str, name: str, lhs: Any, rhs: Any = 0) -> None:
        self.counts[category] += 1
        if isinstance(lhs, (dict, list, tuple)):
            passed = lhs == rhs
            defect = f"lhs={lhs!r}; rhs={rhs!r}"
        else:
            defect_expr = sp.cancel(sp.expand(sp.sympify(lhs) - sp.sympify(rhs)))
            passed = defect_expr == 0
            defect = str(defect_expr)
        if not passed:
            self.failures.append({"category": category, "test": name,
                                  "defect": defect})


def convolution(a: list[Fraction], b: list[Fraction], nmax: int) -> list[Fraction]:
    out = [Fraction(0) for _ in range(nmax + 1)]
    for d in range(1, nmax + 1):
        if a[d]:
            for m in range(1, nmax // d + 1):
                if b[m]:
                    out[d * m] += a[d] * b[m]
    return out


def run_checks() -> Checks:
    checks = Checks()
    a, s, A = sp.symbols('a s A')
    max_degree = 14

    # Bernoulli translation from a direct formal expansion of L(z+a)-L(z).
    direct_translation: dict[int, sp.Expr] = {}
    formula_translation: dict[int, sp.Expr] = {}
    for n in range(1, max_degree + 1):
        direct = ((-1)**n * a**(n+1) / sp.Integer(n+1)
                  + (a-sp.Rational(1, 2)) * (-1)**(n+1) * a**n / n)
        for k in range(1, (n+1)//2 + 1):
            power = 2*k - 1
            coefficient = bernoulli(2*k) / (2*k*(2*k-1))
            direct += coefficient * (
                choose(-sp.Integer(power), n-power) * a**(n-power)
                - (1 if n == power else 0))
        target = ((-1)**(n+1) * (sp.bernoulli(n+1, a) - bernoulli(n+1))
                  / (n*(n+1)))
        direct_translation[n] = sp.expand(direct)
        formula_translation[n] = sp.expand(target)
        checks.equal('Stirling translation', f'degree {n}', direct, target)
        checks.equal('Stirling recurrence', f'degree {n}', direct.subs(a, 1))

    for n in range(1, 21):
        checks.equal('Bernoulli derivative', f'B_{n}',
                     sp.diff(sp.bernoulli(n, a), a), n*sp.bernoulli(n-1, a))
    for m in range(2, 8):
        for n in range(0, 17):
            checks.equal('Bernoulli distribution', f'm={m}, n={n}',
                sum(sp.bernoulli(n, sp.Rational(r, m)) for r in range(m)),
                sp.Rational(m)**(1-n)*bernoulli(n))
        for n in range(1, max_degree+1):
            b = bernoulli(n+1)/(n*(n+1)) if n % 2 else sp.S.Zero
            defect = m*b + sum(formula_translation[n].subs(a, sp.Rational(r, m))
                               for r in range(m)) - b/sp.Integer(m)**n
            checks.equal('Gauss Stirling coefficients', f'm={m}, n={n}', defect)

    def h_coeff(j: int, spectral: sp.Expr) -> sp.Expr:
        if j == 0:
            return 1/(spectral-1)
        if j == 1:
            return sp.Rational(1, 2)
        if j % 2:
            return sp.S.Zero
        return bernoulli(j)/sp.factorial(j)*sp.rf(spectral, j-1)

    h = {j: sp.expand(h_coeff(j, s)) for j in range(15)}
    for j in range(0, 13):
        shift = sum(h[k]*choose(1-s-k, j-k) for k in range(j+1)) - h[j]
        checks.equal('Hurwitz shift', f'degree {j}', shift + (1 if j == 1 else 0))
        checks.equal('Hurwitz parameter derivative', f'degree {j}',
                     (1-s-j)*h[j] + s*h_coeff(j, s+1))
    for m in (2, 3, 4, 5):
        for j in range(0, 11):
            distribution = sum(
                h[k]*m**k*choose(1-s-k, j-k)
                * sum(sp.Integer(r)**(j-k) for r in range(m))
                for k in range(j+1)) - m*h[j]
            checks.equal('Hurwitz distribution', f'm={m}, degree={j}', distribution)

    for m in range(0, 17):
        value = -A**(m+1)/sp.Integer(m+1) + A**m/2
        for k in range(1, (m+1)//2 + 1):
            value += (bernoulli(2*k)/sp.factorial(2*k)*sp.rf(-m, 2*k-1)
                      * A**(m+1-2*k))
        checks.equal('Hurwitz Bernoulli values', f's={-m}', value,
                     -sp.bernoulli(m+1, A)/(m+1))
        checks.equal('Bernoulli polynomial antidifference', f's={-m}',
                     value.subs(A, A+1)-value, -A**m)

    for k in range(1, 17):
        rising = sp.expand(sp.rf(s, 2*k-1))
        deriv0 = sp.diff(rising, s).subs(s, 0)
        checks.equal('Hurwitz log-Gamma bridge', f'k={k}',
                     bernoulli(2*k)/sp.factorial(2*k)*deriv0,
                     bernoulli(2*k)/(2*k*(2*k-1)))
        checks.equal('Hurwitz digamma Laurent constant', f'k={k}',
                     bernoulli(2*k)/sp.factorial(2*k)*rising.subs(s, 1),
                     bernoulli(2*k)/(2*k))

    # Finite Dirichlet-convolution identities; all coefficients are exact.
    nmax = 256
    factors = {n: dict(sp.factorint(n)) for n in range(1, nmax+1)}
    unit = [Fraction(0)]*(nmax+1)
    unit[1] = Fraction(1)
    ones = [Fraction(0)] + [Fraction(1)]*nmax
    mobius = [Fraction(0)] + [Fraction(int(sp.mobius(n))) for n in range(1, nmax+1)]
    inv_product = convolution(mobius, ones, nmax)
    for n in range(1, nmax+1):
        checks.equal('Mobius inversion', f'n={n}', inv_product[n], unit[n])
        # Lambda * 1 = log(n), represented by exact prime-log coefficients.
        log_coefficient: dict[int, int] = {}
        for d in sp.divisors(n):
            ff = factors[int(d)]
            if len(ff) == 1:
                p = next(iter(ff))
                log_coefficient[p] = log_coefficient.get(p, 0) + 1
        checks.equal('Von Mangoldt convolution', f'n={n}', log_coefficient, factors[n])

    prime_product = unit.copy()
    for p in sp.primerange(2, nmax+1):
        geometric = [Fraction(0)]*(nmax+1)
        power = 1
        while power <= nmax:
            geometric[power] = Fraction(1)
            power *= int(p)
        prime_product = convolution(prime_product, geometric, nmax)
    for n in range(1, nmax+1):
        checks.equal('Finite Euler expansion', f'n={n}', prime_product[n], 1)

    logmax = 128
    nonunit = [Fraction(0)] + [Fraction(1)]*logmax
    nonunit[1] = Fraction(0)
    log_series = [Fraction(0)]*(logmax+1)
    power_series = [Fraction(0)]*(logmax+1)
    power_series[1] = Fraction(1)
    k = 1
    while 2**k <= logmax:
        power_series = convolution(power_series, nonunit, logmax)
        for n in range(1, logmax+1):
            log_series[n] += Fraction((-1)**(k+1), k)*power_series[n]
        k += 1
    for n in range(1, logmax+1):
        ff = factors[n]
        expected = Fraction(1, int(next(iter(ff.values())))) if len(ff) == 1 else Fraction(0)
        checks.equal('Formal Euler logarithm', f'n={n}', log_series[n], expected)

    smallmax = 64
    f = [Fraction(0)] + [Fraction((n*n+3*n+1) % 11-5) for n in range(1, smallmax+1)]
    g = [Fraction(0)] + [Fraction((7*n+2) % 13-6) for n in range(1, smallmax+1)]
    hseq = [Fraction(0)] + [Fraction((n*n+1) % 7-3) for n in range(1, smallmax+1)]
    fg = convolution(f, g, smallmax)
    lhs = convolution(fg, hseq, smallmax)
    rhs = convolution(f, convolution(g, hseq, smallmax), smallmax)
    for n in range(1, smallmax+1):
        checks.equal('Convolution associativity sample', f'n={n}', lhs[n], rhs[n])
    for shift in (0, 1, 2, 3):
        ft = [Fraction(0)] + [f[n]/n**shift for n in range(1, smallmax+1)]
        gt = [Fraction(0)] + [g[n]/n**shift for n in range(1, smallmax+1)]
        twisted_product = convolution(ft, gt, smallmax)
        for n in range(1, smallmax+1):
            checks.equal('Shift twist multiplicativity', f'a={shift}, n={n}',
                         twisted_product[n], fg[n]/n**shift)
    for n in range(1, smallmax+1):
        lhs_logs: dict[int, Fraction] = {}
        for d in sp.divisors(n):
            d = int(d)
            m = n//d
            weight = f[d]*g[m]
            for index in (d, m):
                for p, exponent in factors[index].items():
                    lhs_logs[p] = lhs_logs.get(p, Fraction(0)) + weight*exponent
        lhs_logs = {p: v for p, v in lhs_logs.items() if v}
        rhs_logs = {p: fg[n]*e for p, e in factors[n].items() if fg[n]*e}
        checks.equal('Dirichlet derivative Leibniz sample', f'n={n}', lhs_logs, rhs_logs)

    # Abstract exact prime-Jacobian identities. Symbols below stand for logs;
    # the all-real-shift nonsingularity theorem is proved in the article.
    ell = sp.symbols('l1:4')
    e0, e1, e2 = sp.symbols('E Eprime Esecond')
    jac = sp.Matrix([[e0]*3,
                     [e1-e0*t for t in ell],
                     [e2-2*e1*t+e0*t*t for t in ell]])
    expected_det = e0**3 * sp.prod(ell[i]-ell[j] for i in range(3) for j in range(i+1, 3))
    checks.equal('Prime Jacobian factorization', 'single shift, jets 0..2', jac.det(), expected_det)
    x, l2 = sp.symbols('x log2')
    ell4 = sp.symbols('u1:5')
    fresh = (3, 5, 7, 11)
    rows: list[list[sp.Expr]] = []
    blocks: list[sp.Matrix] = []
    base_rows: list[list[sp.Expr]] = []
    for shift in (0, 1):
        E = 1/(1-sp.Rational(1, 2)**shift*x)
        DE = -l2*x*sp.diff(E, x)
        blocks.append(sp.Matrix([[E, 0], [DE, E]]))
        rows.append([sp.Rational(q)**(-shift)*E for q in fresh])
        rows.append([sp.Rational(q)**(-shift)*(DE-E*l)
                     for q, l in zip(fresh, ell4)])
        base_rows.append([sp.Rational(q)**(-shift) for q in fresh])
        base_rows.append([-sp.Rational(q)**(-shift)*l for q, l in zip(fresh, ell4)])
    defect = sp.Matrix(rows) - sp.diag(*blocks)*sp.Matrix(base_rows)
    for i in range(4):
        for j in range(4):
            checks.equal('Prime Jacobian block identity', f'entry ({i},{j})', defect[i, j])

    u = sp.symbols('u', nonzero=True)
    for m in (2, 3, 4):
        phases = [sp.expand_complex(sp.exp(sp.I*sp.pi*sp.Rational(r, m)))
                  for r in range(m)]
        product = sp.prod((u*w - 1/(u*w))/(2*sp.I) for w in phases)
        target = sp.Rational(2)**(1-m)*(u**m-u**(-m))/(2*sp.I)
        checks.equal('Finite sine multiplication', f'm={m}',
                     sp.simplify(sp.expand(product-target)))
    return checks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('verification-rerun.json'))
    parser.add_argument('--overwrite', action='store_true', help='Explicitly permit replacement of output.')
    args = parser.parse_args()
    if args.output.exists() and not args.overwrite:
        parser.error(f'{args.output} already exists; choose another path or use --overwrite')
    start = time.perf_counter()
    checks = run_checks()
    total = sum(checks.counts.values())
    report = {
        'article': 'Gamma and Zeta on the Surcomplex Horizontal Tube',
        'timestamp_utc': datetime.now(timezone.utc).isoformat(),
        'python': platform.python_version(), 'sympy': sp.__version__,
        'elapsed_seconds': round(time.perf_counter()-start, 3),
        'total_checks': total, 'passed': total-len(checks.failures),
        'failed': len(checks.failures),
        'categories': dict(sorted(checks.counts.items())),
        'bounds': {'Stirling_translation_degree': 14, 'Bernoulli_derivative_degree': 20,
                   'Bernoulli_distribution_degree': 16, 'Gauss_m': [2, 3, 4, 5, 6, 7],
                   'Hurwitz_shift_degree': 12, 'Hurwitz_distribution_degree': 10,
                   'Hurwitz_distribution_m': [2, 3, 4, 5],
                   'Hurwitz_negative_integer_m': 16, 'logGamma_bridge_k': 16,
                   'arithmetic_max_n': 256, 'Euler_logarithm_max_n': 128},
        'scope': 'Exact finite symbolic coefficient and arithmetic identities only.',
        'formal_proof_assistant_checked': False,
        'surreal_class_theorems_computationally_verified': False,
        'novelty_certified': False,
        'failures': checks.failures,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(f'{report["passed"]}/{total} checks passed; {report["failed"]} failed.')
    print(f'Report: {args.output.resolve()}')
    return 1 if checks.failures else 0


if __name__ == '__main__':
    sys.exit(main())
