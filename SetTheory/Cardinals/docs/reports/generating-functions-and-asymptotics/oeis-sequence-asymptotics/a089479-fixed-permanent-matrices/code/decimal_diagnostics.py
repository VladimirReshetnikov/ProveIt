#!/usr/bin/env python3
"""Original standard-library Decimal diagnostics, deliberately NOT certificates.

The polynomial truncations and rounded Decimal arithmetic here are not directed
interval arithmetic. Rigorous enclosures come only from certify_constants.py.
"""
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
from math import factorial, comb
import json
from check_fixed_permanent import kernel_poly, expand_kernel, mul, formulas


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def dec(q):
    q = F(q)
    return D(q.numerator) / D(q.denominator)


def evaluate(coefficients, x, derivative=0):
    require(isinstance(derivative, int) and 0 <= derivative <= 4,
            'unsupported derivative')
    result = D(0)
    for n in range(len(coefficients)-1, derivative-1, -1):
        result = result*x + dec(coefficients[n])*D(factorial(n)//factorial(n-derivative))
    return result


def generate():
    with localcontext() as ctx:
        ctx.prec = 90
        count = 70
        kernels, unused = kernel_poly(4)
        S = {2: [F(0), F(0)] + [F(1, n) for n in range(2, count)]}
        S.update({k: expand_kernel(v, count) for k, v in kernels.items()})
        ex = [F((-1)**n, factorial(n)) for n in range(count)]
        E = [v/2**comb(n, 2) for n, v in enumerate(ex)]
        H = {k: [v/2**comb(n, 2) for n, v in enumerate(mul(ex, s, count))]
             for k, s in S.items()}
        correction = mul(ex, mul(S[2], S[2], count), count)
        H[4] = [x-y/2**(comb(n, 2)+1) for n, (x, y) in enumerate(zip(H[4], correction))]
        rho = D('1.49')
        for unused in range(12):
            rho -= evaluate(E, rho)/evaluate(E, rho, 1)
        require(abs(evaluate(E, rho)) < D('1e-85'), 'Newton diagnostic did not converge')
        a = -rho*evaluate(E, rho, 1)
        b = rho**2*evaluate(E, rho, 2)/2
        c = -rho**3*evaluate(E, rho, 3)/6
        h = {k: evaluate(v, rho) for k, v in H.items()}
        hp = {k: evaluate(v, rho, 1) for k, v in H.items()}
        hpp = {k: evaluate(v, rho, 2) for k, v in H.items()}
        P = {1: {1: 1/a}}
        for k in (2, 3):
            P[k] = {2: h[k]/a**2, 1: -rho*hp[k]/a**2 - 2*b*h[k]/a**3}
        P[4] = {
            3: h[2]**2/a**3,
            2: h[4]/a**2-2*rho*h[2]*hp[2]/a**3-3*b*h[2]**2/a**4,
            1: -rho*hp[4]/a**2-2*b*h[4]/a**3
               +rho**2*(hp[2]**2+h[2]*hpp[2])/a**3
               +6*b*rho*h[2]*hp[2]/a**4
               +h[2]**2*(6*b**2/a**5-3*c/a**4)}
        exact = formulas(S, 31, 4)
        ratios = {}
        for k in range(1, 5):
            ratios[k] = {}
            for n in (5, 10, 20, 30):
                polynomial = sum(value*D(comb(n+j-1, j-1)) for j, value in P[k].items())
                ratios[k][n] = format(polynomial*rho**(-n)/dec(exact[k][n]), '.25g')
        return {
            'status': 'DIAGNOSTIC_ONLY',
            'method': 'stdlib Decimal, precision 90; 70 Taylor coefficients; no directed rounding',
            'rho': format(rho, '.60g'), 'a': format(a, '.60g'),
            'h': {k: format(v, '.50g') for k, v in h.items()},
            'P_binomial_basis': {k: {j: format(v, '.50g') for j, v in p.items()} for k, p in P.items()},
            'dominant_term_over_exact_normalized_coefficient': ratios,
            'permanent_two_cycle_size_probabilities': {
                n: format(rho**n/(D(n)*D(2)**comb(n, 2))*evaluate(E, rho/D(2)**n)/h[2], '.35g')
                for n in range(2, 9)}}


if __name__ == '__main__':
    result = generate()
    with open('decimal_diagnostics.json', 'x', encoding='utf-8') as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print('PASS: Decimal diagnostics regenerated (not a rigorous certificate)')
