#!/usr/bin/env python3
"""Independent checks for inherited inverse-argument mixed reductions.

These reconcile the current consolidated manuscript with work already
established on 2026-10-08; they are not counted as newly proved conjectures.
"""

import json
from pathlib import Path

import mpmath as mp


def mixed_parity_formula(a, b, z):
    weight = a+b
    u = {n: mp.re(mp.polylog(n, z)) for n in range(1, weight+1)}
    v = {n: mp.im(mp.polylog(n, z)) for n in range(1, weight+1)}
    component = u if weight % 2 else v
    if weight % 2:
        product = -v[a]*v[b] if a % 2 else u[a]*u[b]
    else:
        product = u[b]*v[a] if a % 2 else u[a]*v[b]
    result = product+mp.binomial(weight, a)*component[weight]/2
    result -= mp.fsum(mp.binomial(weight-j-1, b-1)*mp.zeta(j)*component[weight-j]
                      for j in range(2, a+1, 2))
    result -= mp.fsum(mp.binomial(weight-j-1, a-1)*mp.zeta(j)*component[weight-j]
                      for j in range(2, b+1, 2))
    result *= (-1)**(b+1)
    if weight % 2:
        result -= mp.zeta(weight)/2
    return result


def mixed_quadrature(a, b, z):
    # Direct integral from the nested series; the polylogarithm is on (0,1).
    return z/mp.factorial(a-1)*mp.quad(
        lambda t: (-mp.log(t))**(a-1)*mp.polylog(b, t)/(1-z*t), [0, 1])


def main():
    mp.mp.dps = 65
    rho = mp.exp(2*mp.pi*mp.j/3)
    checks = []
    for name,z in [('i', mp.j), ('rho_squared', mp.conj(rho))]:
        for weight in [5, 6]:
            for b in range(1, weight):
                a = weight-b
                value = mixed_quadrature(a, b, z)
                lhs = mp.re(value) if weight % 2 else mp.im(value)
                rhs = mixed_parity_formula(a, b, z)
                error = abs(lhs-rhs)
                assert error < mp.mpf('1e-58'), (name,a,b,error)
                checks.append({'z': name, 'a': a, 'b': b,
                               'component': 'real' if weight % 2 else 'imaginary',
                               'absolute_residual': mp.nstr(error, 10)})
    pi = mp.pi
    B4, B6 = mp.im(mp.polylog(4,mp.j)), mp.im(mp.polylog(6,mp.j))
    C2,C4,C6 = [mp.im(mp.polylog(n,rho)) for n in [2,4,6]]
    proposed = [
        ('gaussian_real_41', 4, mp.j,
         3*pi**4*mp.log(2)/512+pi**2*mp.zeta(3)/64-mp.mpf(587)*mp.zeta(5)/1024),
        ('gaussian_imaginary_51', 5, mp.j,
         3*B6-5*pi**5*mp.log(2)/3072-pi**2*B4/6-pi**4*mp.catalan/90),
        ('eisenstein_real_41', 4, mp.conj(rho),
         2*pi**4*mp.log(3)/243+2*pi**2*mp.zeta(3)/27-mp.mpf(281)*mp.zeta(5)/162),
        ('eisenstein_imaginary_51', 5, mp.conj(rho),
         -3*C6+pi**5*mp.log(3)/729+pi**2*C4/6+pi**4*C2/90),
    ]
    explicit = []
    for name,a,z,value in proposed:
        expected = mixed_parity_formula(a,1,z)
        error = abs(value-expected)
        assert error < mp.mpf('1e-58'), name
        explicit.append({'name': name, 'absolute_residual': mp.nstr(error,10),
                         'value': mp.nstr(value,55)})
    largest = max(mp.mpf(row['absolute_residual']) for row in checks+explicit)
    report = {'status': 'inherited results, independently rederived',
              'working_decimal_digits': mp.mp.dps,
              'general_formula_quadrature_checks': len(checks),
              'explicit_prior_survivor_checks': len(explicit),
              'maximum_absolute_residual': mp.nstr(largest,12),
              'checks': checks, 'explicit_values': explicit}
    out = Path(__file__).resolve().parent/'mixed_results.json'
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['checks','explicit_values']},indent=2))


if __name__ == '__main__':
    main()
