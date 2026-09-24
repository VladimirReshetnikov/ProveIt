#!/usr/bin/env python3
"""Finite checks accompanying the surcomplex Gamma/zeta article.

These are exact finite algebra and ordinary-complex numerical checks, NOT
proof-assistant verification or an implementation of the surreal field.
Dependencies: Python >=3.10, sympy, mpmath. Run: python verification.py
"""
from __future__ import annotations
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path
from math import factorial
import csv
import json
import platform
import sympy as sp
import mpmath as mp

CUTOFF = Fraction(8)  # retain U**log_2(r) for rational r < 8
Series = dict[Fraction, sp.Expr]
ONE = Fraction(1)


def log2_symbolic(r: Fraction) -> sp.Expr:
    """Encode logarithms using prime factorization; product identities are exact."""
    result = sp.Integer(0)
    for integer, sign in ((r.numerator, 1), (r.denominator, -1)):
        for p, exponent in sp.factorint(integer).items():
            result += sign * exponent * (1 if p == 2 else sp.Symbol(f'L{p}'))
    return sp.expand(result)


def clean(a: Series) -> Series:
    out = {}
    for r, c in a.items():
        c = sp.expand(c)
        if r < CUTOFF and c != 0:
            out[r] = c
    return out


def add(a: Series, b: Series) -> Series:
    out = dict(a)
    for r, c in b.items():
        out[r] = out.get(r, 0) + c
    return clean(out)


def scale(a: Series, coefficient: sp.Expr) -> Series:
    return clean({r: c * coefficient for r, c in a.items()})


def multiply(a: Series, b: Series) -> Series:
    out: dict[Fraction, sp.Expr] = defaultdict(lambda: sp.Integer(0))
    for r, c in a.items():
        for s, d in b.items():
            if r*s < CUTOFF:
                out[r*s] += c*d
    return clean(out)


def near_one_power(w: Series, exponent: sp.Expr) -> Series:
    """(1+w)**exponent, using generalized binomial coefficients."""
    out: Series = {ONE: sp.Integer(1)}
    power: Series = {ONE: sp.Integer(1)}
    coeff = sp.Integer(1)
    for j in range(1, 10):
        power = multiply(power, w)
        if not power:
            break
        coeff = sp.expand(coeff*(exponent-j+1)/j)
        out = add(out, scale(power, coeff))
    else:
        raise RuntimeError('Insufficient binomial truncation depth')
    return out


def multisets(product: Fraction = ONE, minimum_n: int = 3,
              entries: tuple[int, ...] = ()):
    """Enumerate every nonempty multiset with product(n/2) < CUTOFF."""
    for n in range(minimum_n, 2*int(CUTOFF)+1):
        r = product*Fraction(n, 2)
        if r >= CUTOFF:
            break
        new = entries + (n,)
        yield r, new
        yield from multisets(r, n, new)


def inversion_checks() -> tuple[dict, Series]:
    v: Series = {ONE: sp.Integer(1)}
    correction: Series = {}
    multiset_count = 0
    for r, entries in multisets():
        multiset_count += 1
        k = len(entries)
        b = log2_symbolic(r)
        denominator = sp.Integer(1)
        for multiplicity in Counter(entries).values():
            denominator *= factorial(multiplicity)
        v[r] = v.get(r, 0) + (-1)**k*sp.rf(b+2, k-1)/denominator
        correction[r] = correction.get(r, 0) + (-1)**(k+1)*sp.rf(b+1, k-1)/denominator
    v, correction = clean(v), clean(correction)
    w = add(v, {ONE: sp.Integer(-1)})
    residual = dict(w)
    for n in range(3, 2*int(CUTOFF)):
        shifted = multiply({Fraction(n, 2): sp.Integer(1)},
                           near_one_power(w, log2_symbolic(Fraction(n))))
        residual = add(residual, shifted)
    assert not residual, f'Inverse equation failed: {residual}'
    logv: Series = {}
    power: Series = {ONE: sp.Integer(1)}
    for j in range(1, 10):
        power = multiply(power, w)
        if not power:
            break
        logv = add(logv, scale(power, sp.Rational((-1)**(j+1), j)))
    assert not add(logv, correction), 'Logarithmic coefficient formula failed'
    beta = log2_symbolic(Fraction(3, 2))
    expected = {
        Fraction(3, 2): sp.Integer(1),
        Fraction(2): sp.Integer(1),
        Fraction(9, 4): -(1+2*beta)/2,
        Fraction(5, 2): sp.Integer(1),
        Fraction(3): -log2_symbolic(Fraction(3)),
        Fraction(27, 8): (1+3*beta)*(2+3*beta)/6,
        Fraction(7, 2): sp.Integer(1),
        Fraction(15, 4): -(1+log2_symbolic(Fraction(15, 4))),
        Fraction(4): -sp.Rational(1, 2),
    }
    for r, c in expected.items():
        assert sp.expand(correction[r]-c) == 0, f'Wrong displayed coefficient {r}'
    for m in range(1, 31):
        identity = sum((-1)**(k+1)*sp.binomial(m-1, k-1)
                       * sp.rf(m+1, k-1)/sp.factorial(k)
                       for k in range(1, m+1))
        assert sp.simplify(identity-sp.Rational((-1)**(m+1), m)) == 0
    return {
        'integer_sector_identities_checked': 30,
        'cutoff_r_exclusive': str(CUTOFF),
        'cutoff_exponent_exclusive': 3,
        'multisets_enumerated': multiset_count,
        'nonconstant_support_values': len(correction),
        'inverse_equation_residual_zero': True,
        'logarithmic_formula_residual_zero': True,
        'displayed_coefficients_checked': len(expected),
    }, correction


def gamma_hurwitz_checks() -> dict:
    s, a, t = sp.symbols('s a t')
    maxk = 7
    tail = sum(sp.bernoulli(2*k)/sp.factorial(2*k)*sp.rf(s, 2*k-1)
               * a**(-2*k) for k in range(1, maxk+1))
    normalized = 1/(s-1)+1/(2*a)+tail
    at_zero = sp.simplify(a*normalized.subs(s, 0))
    assert sp.simplify(at_zero-(-a+sp.Rational(1, 2))) == 0
    derivative_zero = sp.expand(a*(sp.diff(normalized, s).subs(s, 0)
                                  - sp.log(a)*normalized.subs(s, 0)))
    stirling = (a-sp.Rational(1, 2))*sp.log(a)-a + sum(
        sp.bernoulli(2*k)/(2*k*(2*k-1))*a**(1-2*k)
        for k in range(1, maxk+1))
    assert sp.simplify(derivative_zero-stirling) == 0
    for m in range(11):
        value = sp.expand(a**(1+m)*normalized.subs(s, -m))
        target = -sp.bernoulli(m+1, a)/sp.Integer(m+1)
        assert sp.simplify(value-target) == 0, f'Bernoulli identity m={m}'
    # The logarithmic terms cancel symbolically before this finite expansion.
    order = 13
    delta = (1/t+sp.Rational(1, 2))*sp.log(1+t)-1
    for k in range(1, maxk+1):
        delta += sp.bernoulli(2*k)/(2*k*(2*k-1))*t**(2*k-1)*(
            (1+t)**(1-2*k)-1)
    assert sp.series(delta, t, 0, order).removeO().expand() == 0
    scaled = sp.series(sp.exp(sum(sp.bernoulli(2*k)/(2*k*(2*k-1))
                                 * t**(2*k-1) for k in range(1, 4))),
                       t, 0, 5).removeO()
    assert sp.expand(scaled-(1+t/12+t**2/288-sp.Rational(139, 51840)*t**3
                             -sp.Rational(571, 2488320)*t**4)) == 0
    return {
        'scaled_gamma_coefficients_checked': 4,
        'hurwitz_zero_value': True,
        'lerch_stirling_coefficients_checked': maxk,
        'negative_integer_values_checked': 11,
        'log_gamma_recurrence_zero_through_power': order-1,
    }


def numerical_checks(correction: Series) -> list[dict]:
    mp.mp.dps = 100
    u = mp.mpf('1e-8')
    ln2 = mp.log(2)
    substitutions = {symbol: mp.log(int(str(symbol)[1:]))/ln2
                     for expression in correction.values()
                     for symbol in expression.free_symbols}
    values = {}
    for r, expr in correction.items():
        numeric = expr.evalf(100, subs={sym: sp.Float(str(value), 105)
                                     for sym, value in substitutions.items()})
        values[r] = mp.mpf(str(numeric))
    rows = []
    for k in range(-2, 3):
        s_approx = -mp.log(u)/ln2-2*mp.pi*1j*k/ln2
        for r, coeff in values.items():
            b = mp.log(mp.mpf(r.numerator)/r.denominator)/ln2
            s_approx += coeff*mp.exp(2*mp.pi*1j*k*b)*u**b/ln2
        root = mp.findroot(lambda s: mp.zeta(s)-1-u,
                           (s_approx, s_approx+mp.mpf('1e-12')),
                           tol=mp.mpf('1e-85'), maxsteps=40)
        residual = abs(mp.zeta(s_approx)-1-u)
        error = abs(root-s_approx)
        assert error < mp.mpf('1e-22')
        rows.append({
            'k': k, 'u': '1e-8',
            'root_real': mp.nstr(root.real, 35),
            'root_imag': mp.nstr(root.imag, 35),
            'approximation_error': mp.nstr(error, 12),
            'zeta_residual': mp.nstr(residual, 12),
        })
    return rows


def main() -> None:
    outdir = Path(__file__).resolve().parent
    inverse, coefficients = inversion_checks()
    gamma = gamma_hurwitz_checks()
    numerical = numerical_checks(coefficients)
    result = {
        'status': 'all finite checks passed',
        'scope': ('Exact finite symbolic identities and ordinary-complex numerical '
                  'experiments only; no formal verification of surreal theorems.'),
        'python_version': platform.python_version(),
        'sympy_version': sp.__version__, 'mpmath_version': mp.__version__,
        'inverse': inverse, 'gamma_hurwitz': gamma, 'numerical': numerical,
    }
    (outdir/'verification-results.json').write_text(json.dumps(result, indent=2)+'\n')
    with (outdir/'inverse-coefficients.csv').open('w', newline='') as fp:
        writer = csv.writer(fp)
        writer.writerow(['r', 'exponent_log2_r', 'C_r_prime_log_symbols'])
        for r in sorted(coefficients):
            writer.writerow([str(r), str(log2_symbolic(r)), str(coefficients[r])])
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
