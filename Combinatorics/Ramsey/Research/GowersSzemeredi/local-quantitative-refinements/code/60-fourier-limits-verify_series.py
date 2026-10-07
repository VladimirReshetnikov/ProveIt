#!/usr/bin/env python3
"""Exact polynomial identities and inverse-series checks for the article.

Only fractions.Fraction and other standard-library modules are used.
The checks are finite diagnostics for general identities proved in the text.
"""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def mul(a, b, degree):
    c = [Q(0)] * (degree + 1)
    for i, x in enumerate(a[:degree+1]):
        if x:
            for j, y in enumerate(b[:degree-i+1]):
                if y:
                    c[i+j] += x*y
    return c


def power(a, exponent, degree):
    out = [Q(1)] + [Q(0)] * degree
    for _ in range(exponent):
        out = mul(out, a, degree)
    return out


def compose(f, g, degree):
    out = [Q(0)] * (degree+1)
    gp = [Q(1)] + [Q(0)] * degree
    for k, coefficient in enumerate(f[:degree+1]):
        if k:
            gp = mul(gp, g, degree)
        for j in range(degree+1):
            out[j] += coefficient * gp[j]
    return out


def inverse(f, degree):
    require(f[0] == 0 and f[1] != 0, 'Analytic inverse at zero')
    g = [Q(0)] * (degree+1)
    for k in range(1, degree+1):
        target = Q(1) if k == 1 else Q(0)
        g[k] = (target - compose(f, g, k)[k]) / f[1]
    require(compose(f, g, degree) == [Q(0), Q(1)] + [Q(0)]*(degree-1),
            'Inverse composition identity')
    return g


def B(s):
    out = [Q(0)] + [-Q(comb(s, k)*(-4)**k, 4) for k in range(1, s+1)]
    out[s-1] -= 2**(2*s-3)
    out[s] += 2**(2*s-2)
    require(out[-1] == 0, 'Top-degree cancellation')
    return out


def main():
    records = []
    comparison_orders = list(range(4, 33, 2))
    for s in comparison_orders:
        degree = s+1
        b = B(s)
        p = mul([Q(2), Q(-2)], b, degree)
        signal = [Q(0)] + [-Q(comb(s,k)*(-4)**k) for k in range(1,s+1)]
        c = mul([Q(1,2), Q(-1,2)], signal, degree)
        expected = [Q(0)]*(degree+1)
        expected[s-1] = 2**(2*s-2)
        expected[s] = -3*2**(2*s-2)
        expected[s+1] = 2*2**(2*s-2)
        require([x-y for x,y in zip(c,p)] == expected, 'Two-direction exact gap')

        # Check the positive-basis identity for B_s-F_s after t=2 delta.
        old_core = power([Q(1), Q(-2)], s-2, s)
        old_core[s-2] -= 2**(s-2)
        old = mul([Q(0), Q(s), Q(-2*s)], old_core, s)
        positive_basis = [Q(0)]*(s+1)
        for j in range(3, s-2, 2):
            term = [Q(0)]*j + [Q(2**j)]
            term = mul(term, power([Q(1), Q(-2)], s-j, s), s)
            term[s-1] -= 2**(s-1)
            term[s] += 2**s
            for k in range(s+1):
                positive_basis[k] += Q(comb(s,j),2)*term[k]
        require([x-y for x,y in zip(b,old)] == positive_basis,
                'Strict improvement positive-basis identity')

        n = min(14, max(4, s-2))
        rho = inverse(b,n)
        sigma = inverse(p,n)
        cinv = inverse(c,n)
        require(rho[1] == Q(1,s) and rho[2] == Q(2*(s-1),s*s),
                'One-direction leading coefficients')
        require(sigma[1] == Q(1,2*s) and sigma[2] == Q(2*s-1,4*s*s),
                'Two-direction leading coefficients')
        if s == 4:
            require(rho[3:] == [Q(1),Q(105,32)], 's=4 inverse terms')
            require(sigma[3] == Q(21,128), 's=4 valid two-direction cubic')
        else:
            require(rho[3] == Q(8*(s-1)*(2*s-1),3*s**3), 'Sharp one-direction cubic')
            require(sigma[3] == Q(8*s*s-3*s-2,12*s**3), 'Sharp two-direction cubic')
        through = min(s-2,n)
        require(sigma[:through+1] == cinv[:through+1], 'Sharpness through s-2')
        if s in (4,6,8,16):
            records.append({'s':s,'rho_coefficients':[str(x) for x in rho[1:]],
                            'sigma_coefficients':[str(x) for x in sigma[1:]],
                            'two_direction_sharp_through':through,
                            'prime_lower':str(Q(s-1,s*s)),
                            'prime_upper':str(Q(3*s-2,2*s*s))})
    result = {'status':'passed','arithmetic':'exact fractions.Fraction',
              'orders_checked':comparison_orders,
              'identities':['top-degree cancellation','B_s-F_s positive basis',
                            'C_s-P_s exact gap','inverse compositions',
                            'one- and two-direction coefficients'],
              'selected_inverse_coefficients':records}
    path = Path(__file__).with_name('series_verification.json')
    path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(f'Exact polynomial and inverse checks passed for {len(comparison_orders)} orders.')
    print(path)


if __name__ == '__main__':
    main()
