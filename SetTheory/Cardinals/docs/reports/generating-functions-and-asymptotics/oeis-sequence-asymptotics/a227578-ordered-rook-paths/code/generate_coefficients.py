#!/usr/bin/env python3
"""Finite exact generator for fixed-dimension ordered rook asymptotics.

This implements the article's radial-root and Gaussian-moment algorithm.
Example: python code/generate_coefficients.py --k 3 --order 2
Use --k symbolic for symbolic-k expressions. Complexity rises rapidly with order.
No counting recurrence is assumed. Requires SymPy 1.14.0.
"""
import argparse
import json
from functools import lru_cache
import sympy as sp


def generate(k, order):
    if order < 0:
        raise ValueError('order must be nonnegative')
    if isinstance(k, int):
        if k < 2:
            raise ValueError('dimension must be at least two')
        k = sp.Integer(k)
    t, z = sp.symbols('t z')
    degree = 2 * order + 2
    P = {0: k, 1: sp.Integer(0)}
    P.update({j: sp.Symbol('P' + str(j)) for j in range(2, degree + 1)})
    q = 1 / (k + 1)
    derivatives, h = [], z / (1 - z)
    for _ in range(degree + 1):
        derivatives.append(sp.factor(h.subs(z, q)))
        h = z * sp.diff(h, z)
    mu = derivatives[1]
    beta = derivatives[2] / mu

    def trunc(expr, n):
        return sp.Add(*(c * t ** e[0] for e, c in sp.Poly(sp.expand(expr), t).terms() if e[0] <= n))

    def summed_power(sigma, m, n):
        powers = [sp.Integer(1)]
        for _ in range(m):
            powers.append(trunc(powers[-1] * sigma, n))
        return trunc(sum(sp.binomial(m, j) * powers[m-j] * (sp.I*t)**j * P[j]
                         for j in range(m + 1)), n)

    sigma, sigmas = sp.Integer(0), {}
    for r in range(2, degree + 1):
        residual = sum(derivatives[m] / sp.factorial(m) * summed_power(sigma, m, r)
                       for m in range(1, r + 1))
        sr = sp.factor(-sp.expand(residual).coeff(t, r) / (k * mu))
        sigmas[r] = sr
        sigma += sr * t ** r

    top = 2 * order
    U = trunc(sum(derivatives[m+1] / sp.factorial(m) * summed_power(sigma, m, top)
                  for m in range(1, top + 1)) / (k * mu), top)
    log_radial = trunc(sum(sp.Rational((-1)**j, j) * trunc(U ** j, top)
                           for j in range(1, top + 1)), top)
    log_denominator = trunc((k - 1) * sum(derivatives[m-1] / sp.factorial(m)
                            * summed_power(sigma, m, top) for m in range(1, top + 1)), top)
    w = sp.Symbol('w')
    log_sinh = sp.series(sp.log(sp.sinh(w)/w), w, 0, top+1).removeO()
    log_vandermonde = sp.Integer(0)
    for r in range(1, order+1):
        m = 2*r
        difference_power_sum = sum((-1)**j * sp.binomial(m, j) * P[j] * P[m-j]
                                   for j in range(m+1)) / 2
        log_vandermonde += 2 * log_sinh.coeff(w, m) * (sp.I*t/2)**m * difference_power_sum
    log_B = trunc(log_radial + log_denominator + log_vandermonde
                  - k*sigma/t**2 + beta*P[2]/2, top)
    assert sp.simplify(log_B.coeff(t, 0)) == 0
    logs = {r: sp.factor(log_B.coeff(t, r)) for r in range(1, top+1)}
    exp_coeff = {0: sp.Integer(1)}
    for r in range(1, top+1):
        exp_coeff[r] = sp.expand(sum(j * logs[j] * exp_coeff[r-j] for j in range(1, r+1)) / r)

    @lru_cache(None)
    def trace_moment(parts):
        """Trace-zero Gaussian integration by parts at beta=1."""
        parts = tuple(sorted(parts))
        if 1 in parts:
            return sp.Integer(0)
        zeros = parts.count(0)
        if zeros:
            return k**zeros * trace_moment(tuple(v for v in parts if v))
        if not parts:
            return sp.Integer(1)
        if sum(parts) % 2:
            return sp.Integer(0)
        m, *tail = parts
        rest = tuple(tail)
        ans = sum(trace_moment(tuple(sorted((j, m-2-j)+rest))) for j in range(m-1))
        ans -= sp.Rational(m-1, 1)/k * trace_moment(tuple(sorted((m-2,)+rest)))
        for i, r in enumerate(rest):
            other = rest[:i] + rest[i+1:]
            ans += r * (trace_moment(tuple(sorted((m+r-2,)+other)))
                        - trace_moment(tuple(sorted((m-1, r-1)+other))) / k)
        return sp.factor(ans)

    coefficients = [sp.Integer(1)]
    for j in range(1, order+1):
        ans = sp.Integer(0)
        for powers, coefficient in sp.Poly(exp_coeff[2*j], *[P[r] for r in range(2, degree+1)]).terms():
            parts = tuple(r for r, exponent in zip(range(2, degree+1), powers) for _ in range(exponent))
            ans += coefficient * trace_moment(parts) / beta**(sum(parts)//2)
        coefficients.append(sp.factor(ans))
    return {'k': str(k), 'order': order, 'coefficients': [str(v) for v in coefficients],
            'sigma': {str(j): str(v) for j, v in sigmas.items()},
            'log_amplitude': {str(j): str(v) for j, v in logs.items()}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--k', default='3', help='integer >=2, or symbolic')
    parser.add_argument('--order', type=int, default=2)
    parser.add_argument('--output')
    args = parser.parse_args()
    k = sp.Symbol('k') if args.k == 'symbolic' else int(args.k)
    result = generate(k, args.order)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        with open(args.output, 'w') as stream:
            stream.write(text)
    else:
        print(text, end='')

if __name__ == '__main__':
    main()
