"""Exact formal verification of the logarithmic and inverse sectors.

The dictionary key (i, j) represents z**i * u**j, where z = 1/L and
u = pi**2/r**2. All arithmetic is over Fraction; SymPy is used only for
rational inverse-function derivatives and readable output.

Run: python formal.py --order 8
This is finite algebraic verification, not an analytic error-bound proof.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from math import comb
from pathlib import Path
from typing import TypeAlias

import sympy as sp

Series: TypeAlias = dict[tuple[int, int], F]
N = 10  # Truncation includes two guard coefficients; set by main().
ONE: Series = {(0, 0): F(1)}


def clean(a: Series) -> Series:
    return {key: value for key, value in a.items() if value and -1 <= key[0] <= N}


def add(a: Series, b: Series) -> Series:
    result = a.copy()
    for key, value in b.items():
        result[key] = result.get(key, F(0)) + value
    return clean(result)


def scale(a: Series, factor: F | int) -> Series:
    return clean({key: value * factor for key, value in a.items()})


def sub(a: Series, b: Series) -> Series:
    return add(a, scale(b, -1))


def mul(a: Series, b: Series) -> Series:
    result: Series = {}
    for (i, j), value in a.items():
        for (k, ell), other in b.items():
            if -1 <= i + k <= N:
                key = (i + k, j + ell)
                result[key] = result.get(key, F(0)) + value * other
    return clean(result)


def power(a: Series, exponent: int) -> Series:
    if exponent < 0:
        raise ValueError('Use binom_series for inversion of a unit series.')
    result = ONE.copy()
    for _ in range(exponent):
        result = mul(result, a)
    return result


def shift(a: Series, amount: int) -> Series:
    return clean({(i + amount, j): value for (i, j), value in a.items()})


def binom_series(a: Series, exponent: F | int) -> Series:
    """Return (1+a)**exponent, where a has positive z valuation."""
    result, term, coefficient = ONE.copy(), ONE.copy(), F(1)
    for k in range(1, N + 2):
        term = mul(term, a)
        coefficient *= F(exponent - k + 1, k)
        result = add(result, scale(term, coefficient))
    return result


def log1p(a: Series) -> Series:
    result: Series = {}
    term = ONE.copy()
    for k in range(1, N + 2):
        term = mul(term, a)
        result = add(result, scale(term, F((-1) ** (k + 1), k)))
    return result


def exp_series(a: Series) -> Series:
    result, term, coefficient = ONE.copy(), ONE.copy(), F(1)
    for k in range(1, N + 2):
        term = mul(term, a)
        coefficient /= k
        result = add(result, scale(term, coefficient))
    return result


def dz(a: Series) -> Series:
    return clean({(i - 1, j): i * value for (i, j), value in a.items() if i})


def compose(a: Series, b: Series) -> Series:
    """Substitute b for z; a must have no negative z powers."""
    result: Series = {}
    for (i, j), value in a.items():
        term = power(b, i)
        result = add(result, {(k, ell + j): v * value for (k, ell), v in term.items()})
    return result


def coeff_expr(a: Series, i: int) -> sp.Expr:
    u = sp.Symbol('u')
    return sp.factor(sum(sp.Rational(v.numerator, v.denominator) * u**j
                         for (k, j), v in a.items() if k == i))


def sommerfeld_series() -> Series:
    """Generate C_r(v)/r, with the temporary z variable equal to 1/v.

    Recursion: Y^(j)(0) = [(y/(v*y-1) d/dy)^j y] at y=1.
    No stored correction coefficients enter this calculation.
    """
    y, v = sp.symbols('y v')
    derivative = y
    result: Series = {}
    for j in range(1, N + 2):
        derivative = sp.cancel(y * sp.diff(derivative, y) / (v * y - 1))
        if j % 2 == 0:
            continue
        ell = (j + 1) // 2
        denominator_power = 2 * j - 1
        numerator = sp.Poly(sp.cancel(derivative.subs(y, 1)
                                      * (v - 1)**denominator_power), v)
        eta_normalized = sp.simplify(2 * (1 - sp.Rational(1, 2)**(j))
                                      * sp.zeta(j + 1) / sp.pi**(j + 1))
        prefactor = F(int(sp.numer(eta_normalized)), int(sp.denom(eta_normalized)))
        for (degree,), coefficient in numerator.terms():
            initial_power = denominator_power - degree
            for offset in range(max(0, N - initial_power + 1)):
                key = (initial_power + offset, ell)
                term = prefactor * F(int(coefficient)) * comb(denominator_power + offset - 1, offset)
                result[key] = result.get(key, F(0)) + term
    return clean(result)


def build() -> tuple[Series, Series, Series, Series]:
    c = sommerfeld_series()
    geometric = {(i, 0): F(1) for i in range(N + 1)}
    # d(v)=2(c+c')/(v-1); d/dv = -z^2 d/dz.
    d = scale(mul(shift(sub(c, shift(dz(c), 2)), 1), geometric), 2)
    delta: Series = {}
    for _ in range(N + 2):
        inverse_v = shift(binom_series(shift(delta, 1), -1), 1)
        delta = scale(log1p(compose(d, inverse_v)), F(-1, 2))
    inverse_v = shift(binom_series(shift(delta, 1), -1), 1)
    cv, dv = compose(c, inverse_v), compose(d, inverse_v)
    v = add({(-1, 0): F(1)}, delta)
    numerator = add(sub(v, ONE), add(cv, scale(mul(v, dv), F(1, 2))))
    entropy = mul(numerator, binom_series(dv, F(-1, 2)))
    # Check the defining saddle reversion, independently of its displayed coefficients.
    residual = add(delta, scale(log1p(dv), F(1, 2)))
    assert not {k: val for k, val in residual.items() if k[0] <= N - 2}
    return c, d, delta, entropy


def inverse_ratio(entropy: Series) -> tuple[Series, Series]:
    B = {k: value for k, value in entropy.items() if k[0] >= 1}
    h: Series = {}
    geometric = {(i, 0): F(1) for i in range(N + 1)}
    for _ in range(N + 2):
        inverse_L = shift(binom_series(shift(h, 1), -1), 1)
        Bh = compose(B, inverse_L)
        h = scale(log1p(mul(shift(add(h, Bh), 1), geometric)), -1)
    # Equivalent defining equation exp(h)*(L0+h-1+B(L0+h)) = L0-1.
    inverse_L = shift(binom_series(shift(h, 1), -1), 1)
    lhs = mul(exp_series(h), add(add({(-1, 0): F(1), (0, 0): F(-1)}, h),
                                compose(B, inverse_L)))
    residual = sub(lhs, {(-1, 0): F(1), (0, 0): F(-1)})
    assert not {k: val for k, val in residual.items() if k[0] <= N - 2}
    return h, exp_series(scale(h, 2))


def main() -> None:
    global N
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=8)
    args = parser.parse_args()
    if not 2 <= args.order <= 16:
        parser.error('Choose an order from 2 to 16 (symbolic cost grows with order).')
    N = args.order + 2
    c, d, delta, entropy = build()
    h, ratio = inverse_ratio(entropy)
    u = sp.Symbol('u')
    known_b = {1: u/6, 2: u/6, 3: u*(12-u)/72, 4: u*(3*u+20)/120,
               5: u*(5*u**2+492*u+360)/2160,
               6: u*(1973*u**2+34020*u+7560)/45360,
               7: -u*(175*u**3-194616*u**2-650160*u-60480)/362880,
               8: u*(157813*u**3+3664584*u**2+3916080*u+181440)/1088640}
    known_d = {2: -u/3, 3: -u/3, 4: u*(u-3)/9, 5: u*(u-10)/30,
               6: -u*(20*u**2+231*u+180)/540,
               7: -u*(668*u**2+17955*u+3780)/11340,
               8: u*(140*u**3-9339*u**2-43470*u-3780)/11340}
    for j in range(1, min(args.order, 8)+1):
        assert sp.expand(coeff_expr(entropy, j) - known_b[j]) == 0
    for j in range(2, min(args.order, 8)+1):
        assert sp.expand(coeff_expr(ratio, j) - known_d[j]) == 0
    output = {'order': args.order,
              'forward': {str(j): str(coeff_expr(entropy, j)) for j in range(1,args.order+1)},
              'inverse': {str(j): str(coeff_expr(ratio, j)) for j in range(2,args.order+1)},
              'checks': 'Defining formal identities and displayed coefficients passed.'}
    path = Path(__file__).resolve().parent / 'formal_coefficients.json'
    path.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
