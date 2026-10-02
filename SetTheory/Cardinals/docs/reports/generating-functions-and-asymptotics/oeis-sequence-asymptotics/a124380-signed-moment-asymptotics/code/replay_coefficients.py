#!/usr/bin/env python3
"""Exact finite A124380 relative/logarithmic coefficient generator.

Usage: python replay_coefficients.py --order 4
Requires SymPy; performs no network or external-service operations.
It prints JSON to stdout and writes no files. All coefficients are rational
polynomials in L. The requested order is finite; no convergence is asserted.
"""
import argparse
from functools import lru_cache
import json
import sympy as s


def coefficients(order):
    if not isinstance(order, int) or order < 0:
        raise ValueError('order must be a nonnegative integer')
    L, y = s.symbols('L y')
    mu = (L + 2) / 4

    @lru_cache(None)
    def moment(d):
        if d == 0:
            return s.Integer(1)
        if d == 1:
            return mu
        return s.expand(mu * moment(d - 1) + s.Rational(d - 1, 4) * moment(d - 2))

    phase = [s.Integer(0)]
    relative_integrand = [s.Integer(1)]
    relative = [s.Integer(1)]
    logarithmic = [s.Integer(0)]
    for j in range(1, order + 1):
        correction = sum(
            s.bernoulli(2 * r) / (2 * r * (2 * r - 1))
            * s.binomial(j - 1, 2 * r - 2) * y ** (j - 2 * r + 1)
            for r in range(1, (j + 1) // 2 + 1)
        )
        phase.append(s.expand((-1) ** (j + 1) * (
            2 * y ** (j + 2) / (j + 2)
            + y ** (j + 1) / (j * (j + 1))
            + y ** j / (2 * j) - correction)))
        relative_integrand.append(s.expand(sum(
            ell * phase[ell] * relative_integrand[j - ell]
            for ell in range(1, j + 1)) / j))
        relative.append(s.factor(sum(
            coefficient * moment(powers[0])
            for powers, coefficient in s.Poly(relative_integrand[j], y).terms())))
        logarithmic.append(s.factor(relative[j] - sum(
            ell * logarithmic[ell] * relative[j - ell]
            for ell in range(1, j)) / j))
        if s.degree(relative[j], L) > 3 * j:
            raise ArithmeticError('unexpected relative-polynomial degree')
    return L, phase, relative, logarithmic


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=4)
    args = parser.parse_args()
    if args.order < 0:
        parser.error('--order must be nonnegative')
    L, phase, relative, logarithmic = coefficients(args.order)
    print(json.dumps({
        'sequence': 'A124380',
        'parameter': 'x=sqrt(n/2), L=log(x)',
        'leading': '(exp(1/2)/2)*x*exp(x^2*(2*L-1)+x*(L+1)+L^2/8)',
        'relative_coefficients': [str(v) for v in relative],
        'logarithmic_coefficients': [str(v) for v in logarithmic],
        'fixed_order_relative_remainder': 'O_R((1+L)^(3*R+3)/x^(R+1))',
        'sympy_version': s.__version__,
    }, indent=2))


if __name__ == '__main__':
    main()
