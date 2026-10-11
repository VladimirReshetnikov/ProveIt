#!/usr/bin/env python3
"""Independent numerical diagnostics for Sections 2--5.

The finite part is evaluated by a convergent local Taylor integral plus
ordinary quadrature away from zero. No spectral formula is used in that
evaluation. Diagnostics use arbitrary precision, not interval arithmetic.
"""
from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path
import time
import mpmath as mp

mp.mp.dps = 90
START = time.time()
TAYLOR_ORDER = 160
records = []


@lru_cache(None)
def zeta(k):
    return mp.zeta(k)


def convolution(a, b, degree):
    out = [mp.mpf(0)] * (degree + 1)
    for j, aj in enumerate(a):
        if not aj:
            continue
        for k in range(min(len(b) - 1, degree - j) + 1):
            if b[k]:
                out[j + k] += aj * b[k]
    return out


@lru_cache(None)
def factored_polygamma(r, degree):
    """x**(r+1)*psi^(r)(x), as a convergent polynomial truncation."""
    out = [mp.mpf(0)] * (degree + 1)
    out[0] = (-1) ** (r + 1) * mp.factorial(r)
    if r == 0:
        out[1] = -mp.euler
    for ell in range(max(2, r + 1), degree + 1):
        out[ell] = ((-1) ** ell * zeta(ell)
                    * mp.factorial(ell - 1) / mp.factorial(ell - r - 1))
    return tuple(out)


@lru_cache(None)
def monomial_coefficients(orders):
    weight = sum(r + 1 for r in orders)
    degree = weight + TAYLOR_ORDER
    values = [mp.mpf(1)]
    for r in orders:
        values = convolution(values, factored_polygamma(r, degree), degree)
    return weight, tuple(values)


def psi(r, x):
    return mp.digamma(x) if r == 0 else mp.polygamma(r, x)


def monomial_value(orders, x):
    return mp.fprod(psi(r, x) for r in orders)


def finite_part(orders, split):
    weight, coefficients = monomial_coefficients(tuple(orders))
    terms = []
    for j, coefficient in enumerate(coefficients):
        k = j - weight
        if k == -1:
            terms.append(coefficient * mp.log(split))
        else:
            terms.append(coefficient * split ** (k + 1) / (k + 1))
    local = mp.fsum(terms)
    ordinary = mp.quad(lambda x: monomial_value(orders, x),
                       [split, mp.mpf('0.5'), 1])
    return local + ordinary


def record(name, left, right, tolerance='1e-65'):
    error = abs(left - right)
    relative = error / max(mp.mpf(1), abs(left), abs(right))
    assert relative < mp.mpf(tolerance), (name, mp.nstr(relative, 15))
    records.append({'name': name, 'left': mp.nstr(left, 82),
                    'right': mp.nstr(right, 82),
                    'absolute_residual': mp.nstr(error, 12),
                    'relative_residual': mp.nstr(relative, 12),
                    'passed': True})


def bilinear_formula(r, s):
    h = r + s
    alpha, beta = (-1) ** (r + 1), (-1) ** (s + 1)
    harmonic = lambda n: mp.fsum(mp.mpf(1) / k for k in range(1, n + 1))
    return mp.factorial(h) * (
        (alpha + beta) * mp.diff(mp.zeta, h + 1)
        + (alpha * (harmonic(h) - harmonic(s))
           + beta * (harmonic(h) - harmonic(r))) * zeta(h + 1))


def derivative_monomials(orders):
    for i in range(len(orders)):
        result = list(orders)
        result[i] += 1
        yield tuple(sorted(result))


def endpoint(orders):
    weight, coefficients = monomial_coefficients(tuple(orders))
    return monomial_value(orders, 1) - coefficients[weight]


def primitive_kernel_bracket(t, z):
    # A local series prevents catastrophic cancellation at quadrature's
    # arbitrarily small endpoint nodes.
    if abs(t) < mp.mpf('0.00001'):
        return mp.fsum(((-1) ** k - (-z) ** k) * t ** (k - 1)
                       / mp.factorial(k) for k in range(2, 30))
    return (mp.expm1(-t) - mp.expm1(-z * t)) / t - (z - 1)


def primitive_single_polygamma(r, z):
    j = r + 1
    pole = (-1) ** (r + 1) * mp.factorial(r)
    kappa = -mp.euler if r == 0 else pole * zeta(r + 1)
    elementary = mp.log(z) if j == 1 else (z ** (1 - j) - 1) / (1 - j)
    integral = mp.quad(
        lambda t: t ** (j - 1) * primitive_kernel_bracket(t, z)
        / mp.expm1(t), [0, mp.mpf('0.1'), 1, 5, 20, mp.inf])
    return pole * elementary + kappa * (z - 1) + pole / mp.factorial(j - 1) * integral


def main():
    pairs = [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6),
             (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3), (2, 4)]
    for r, s in pairs:
        a = finite_part((r, s), mp.mpf(1) / 4)
        b = finite_part((r, s), mp.mpf(1) / 5)
        record(f'bilinear_{r}_{s}', a, bilinear_formula(r, s))
        record(f'split_stability_{r}_{s}', a, b)
        print(f'Passed bilinear ({r},{s}) and independent split check.', flush=True)
    record('scalar_psi_square', finite_part((0, 0), mp.mpf(1) / 4),
           2 * mp.stieltjes(1) - 2 * zeta(2))
    for orders in [(0, 1), (1, 2), (0, 0, 1), (0, 1, 2)]:
        value = mp.fsum(finite_part(term, mp.mpf(1) / 5)
                        for term in derivative_monomials(orders))
        record('endpoint_' + '_'.join(map(str, orders)), value, endpoint(orders))
    for z in [mp.mpf('0.7'), mp.mpf('2.2'), mp.mpc('0.7', '0.3')]:
        for r in [0, 1, 2]:
            computed = primitive_single_polygamma(r, z)
            known = (mp.loggamma(z) if r == 0
                     else psi(r - 1, z) - psi(r - 1, 1))
            record(f'primitive_r{r}_z{z}', computed, known)
    # The shifted derivative is checked with a nonlinear mixed polynomial,
    # integrating directly before differentiating with respect to the shift.
    a = mp.mpf('0.8')
    for orders in [(0, 0, 1), (1, 1)]:
        shifted = lambda v: mp.quad(lambda x: monomial_value(orders, v + x), [0, 1])
        left = mp.diff(shifted, a)
        right = monomial_value(orders, a + 1) - monomial_value(orders, a)
        record('shift_derivative_' + '_'.join(map(str, orders)), left, right)
    result = {'status': 'passed', 'arithmetic': 'mpmath floating point, not intervals',
              'mpmath_version': mp.__version__, 'working_decimal_digits': mp.mp.dps,
              'taylor_order': TAYLOR_ORDER, 'assertions': len(records),
              'maximum_relative_residual': mp.nstr(max(mp.mpf(r['relative_residual'])
                                                       for r in records), 12),
              'seconds': round(time.time() - START, 3), 'checks': records}
    target = Path(__file__).resolve().parent.parent / 'results/differential_numeric.json'
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'checks'}, indent=2))


if __name__ == '__main__':
    main()
