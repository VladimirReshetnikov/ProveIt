#!/usr/bin/env python3
"""Exact and independent quadrature checks for the accompanying proofs.

Dependencies: mpmath, sympy.  Numerical checks are diagnostics; the proofs
are in theorems.tex.  No PSLQ, fitted coefficients, or numeric rank is used.
"""

from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent


def parity_components(weight, z):
    """The finite formula, with all boundary singles evaluated directly."""
    u = {n: mp.re(mp.polylog(n, z)) for n in range(1, weight + 1)}
    v = {n: mp.im(mp.polylog(n, z)) for n in range(1, weight + 1)}
    odd = weight % 2
    component = u if odd else v
    triangular = {}
    for p in range(1, weight):
        q = weight - p
        if odd:
            product = -v[p] * v[q] if p % 2 else u[p] * u[q]
        else:
            product = u[q] * v[p] if p % 2 else u[p] * v[q]
        val = product
        val += mp.fsum(
            mp.binomial(weight-j-1, q-1) * mp.zeta(j) * component[weight-j]
            for j in range(3, p+1, 2)
        )
        val -= mp.fsum(
            mp.binomial(weight-j-1, p-1) * mp.zeta(j) * component[weight-j]
            for j in range(3, q+1, 2)
        )
        val -= (mp.binomial(weight-1, q)-mp.binomial(weight-1, p)) * component[weight]/2
        if odd:
            val -= (-1)**p * mp.zeta(weight)/2
        triangular[p] = val
    return {
        (weight-b, b): mp.fsum(
            (-1)**(b-p) * mp.binomial(weight-p-1, b-p) * triangular[p]
            for p in range(1, b+1)
        )
        for b in range(1, weight)
    }


def double_quadrature(a, b, z):
    """Independent Mellin integral for the defining nested series."""
    return z/mp.factorial(a-1) * mp.quad(
        lambda t: (-mp.log(t))**(a-1) * mp.polylog(b, z*t)/(1-z*t),
        [0, mp.mpf('0.25'), 1],
    )


def one_two_quadrature(r, s, z):
    """Direct iterated integral with one zero letter."""
    alpha = -mp.log(1-z)
    return mp.quad(
        lambda t: (alpha+mp.log(1-z*t))**r * (-mp.log(1-z*t))**(s+1)/t,
        [0, 1],
    )/(mp.factorial(r)*mp.factorial(s+1))


def height_one_formula(d, z):
    a = mp.log(1-z)
    return (mp.zeta(d+1) + (-1)**d * a**d * mp.log(z)/mp.factorial(d)
            + mp.fsum((-1)**(k+1)*a**k/mp.factorial(k)*mp.polylog(d+1-k, 1-z)
                      for k in range(d)))


def one_two_formula(r, s, z):
    alpha = -mp.log(1-z)
    return mp.fsum(
        (-1)**j * mp.binomial(s+j+1, j) * alpha**(r-j)/mp.factorial(r-j)
        * height_one_formula(s+j+1, z)
        for j in range(r+1)
    )


L = sp.Symbol('L', real=True)
G = sp.Symbol('G', real=True)


def symbolic_beta(n):
    if n == 2:
        return G
    if n % 2 == 0:
        return sp.Symbol(f'B{n}', real=True)
    k = (n-1)//2
    return (-1)**k * sp.euler(2*k)*sp.pi**n/(4**(k+1)*sp.factorial(2*k))


def symbolic_gaussian(weight):
    u = {n: -L/2 if n == 1 else -sp.Rational(1, 2)**n *
         (1-sp.Rational(1, 2)**(n-1))*sp.zeta(n)
         for n in range(1, weight+1)}
    v = {n: symbolic_beta(n) for n in range(1, weight+1)}
    component = u if weight % 2 else v
    triangular = {}
    for p in range(1, weight):
        q = weight-p
        if weight % 2:
            product = -v[p]*v[q] if p % 2 else u[p]*u[q]
        else:
            product = u[q]*v[p] if p % 2 else u[p]*v[q]
        val = product
        val += sum(sp.binomial(weight-j-1, q-1)*sp.zeta(j)*component[weight-j]
                   for j in range(3, p+1, 2))
        val -= sum(sp.binomial(weight-j-1, p-1)*sp.zeta(j)*component[weight-j]
                   for j in range(3, q+1, 2))
        val -= (sp.binomial(weight-1, q)-sp.binomial(weight-1, p))*component[weight]/2
        if weight % 2:
            val -= sp.Rational((-1)**p, 2)*sp.zeta(weight)
        triangular[p] = sp.expand(val)
    return {(weight-b, b): sp.expand(sum(
                (-1)**(b-p)*sp.binomial(weight-p-1, b-p)*triangular[p]
                for p in range(1, b+1)))
            for b in range(1, weight)}


def exact_checks():
    B4, B6 = symbolic_beta(4), symbolic_beta(6)
    pi, z3, z5 = sp.pi, sp.zeta(3), sp.zeta(5)
    expected = {
        (5, 1): (-64*pi**3*z3-527*pi*z5+4096*B6)/2048,
        (4, 2): (96*pi**3*z3-32*pi**2*B4+1581*pi*z5-8448*B6)/1536,
        (3, 3): (-3*pi**3*z3+64*pi**2*B4-1581*pi*z5+4608*B6)/1024,
        (2, 4): (-14*pi**4*G+135*pi**3*z3-1440*pi**2*B4+23715*pi*z5-69120*B6)/23040,
        (1, 5): (-150*pi**5*L+56*pi**4*G-270*pi**3*z3+1920*pi**2*B4-675*pi*z5)/92160,
    }
    actual = symbolic_gaussian(6)
    for index, value in expected.items():
        assert sp.expand(actual[index]-value) == 0, index

    # Derive the triple identities by the analytic antiderivative/inversion
    # path; compare with the three equations transcribed from the manuscript.
    l3, l4, m4 = sp.symbols('lambda3 lambda4 mu4', real=True)
    a, c = L/2-sp.I*pi/4, L/2+3*sp.I*pi/4
    r2 = 5*pi**2/96-L**2/8+sp.I*(G-pi*L/8)
    r3 = sp.Rational(35,64)*z3-5*pi**2*L/192+L**3/48+sp.I*l3
    s2 = -r2-pi**2/6-c**2/2
    s3 = r3-pi**2*c/6-c**3/6
    s4 = -(m4+sp.I*l4)-7*pi**4/360-pi**2*c**2/12-c**4/24
    f21 = sp.expand(z3+a**2*sp.I*pi/4+a*s2-s3)
    f211 = sp.expand(sp.zeta(4)-s4+a*s3-a**2*s2/2-a**3*sp.I*pi/12)
    f121 = sp.expand(-a*f21-3*f211)
    f112 = sp.expand((-pi**2/48+sp.I*G)*a**2/2+2*a*f21+3*f211)
    triples = {
        (2,1,1): (sp.im(f211), l4+L*l3/2-G*(pi**2-4*L**2)/32-pi*(8*L**3+105*z3)/768),
        (1,2,1): (sp.im(f121), -3*l4-L*l3+G*(pi**2-4*L**2)/32-3*pi**3*L/256+pi*(2*L**3+67*z3)/128),
        (1,1,2): (sp.im(f112), 3*l4+L*l3/2+5*pi**3*L/192-163*pi*z3/256),
    }
    for index, (derived, target) in triples.items():
        assert sp.expand(derived-target) == 0, index
    return {'manuscript_double_identities_proved_and_checked': 5,
            'manuscript_triple_identities_proved_and_checked': 3,
            'symbolic_status': 'all differences exactly zero'}


def main():
    mp.mp.dps = 65
    exact = exact_checks()
    checks = []
    for name, z in [('i', mp.j), ('rho', mp.exp(2*mp.pi*mp.j/3))]:
        for weight in [2, 3, 4, 5, 6, 8]:
            for (a, b), rhs in parity_components(weight, z).items():
                value = double_quadrature(a, b, z)
                lhs = mp.re(value) if weight % 2 else mp.im(value)
                error = abs(lhs-rhs)
                assert error < mp.mpf('1e-58'), (name, a, b, error)
                checks.append({'family': 'double', 'z': name, 'a': a, 'b': b,
                               'component': 'real' if weight % 2 else 'imaginary',
                               'absolute_residual': mp.nstr(error, 8)})
    # A non-cyclotomic special angle checks that the formula is not merely
    # a root-of-unity coefficient fit.
    z = mp.exp(mp.j*mp.sqrt(2))
    for (a, b), rhs in parity_components(6, z).items():
        error = abs(mp.im(double_quadrature(a, b, z))-rhs)
        assert error < mp.mpf('1e-58'), (a, b, error)
        checks.append({'family': 'double', 'z': 'exp(i sqrt(2))', 'a': a, 'b': b,
                       'component': 'imaginary', 'absolute_residual': mp.nstr(error, 8)})
    for r in range(5):
        for s in range(3):
            error = abs(one_two_quadrature(r, s, mp.j)-one_two_formula(r, s, mp.j))
            assert error < mp.mpf('1e-58'), (r, s, error)
            checks.append({'family': 'one_two', 'z': 'i', 'initial_ones': r,
                           'final_ones': s, 'absolute_residual': mp.nstr(error, 8)})
    max_residual = max(mp.mpf(c['absolute_residual']) for c in checks)
    report = {'working_decimal_digits': mp.mp.dps, **exact,
              'numerical_check_count': len(checks),
              'maximum_absolute_residual': mp.nstr(max_residual, 12),
              'method': 'direct Mellin/iterated-integral quadrature compared with finite symbolic formulas',
              'checks': checks}
    (ROOT/'depth_results.json').write_text(json.dumps(report, indent=2)+'\n')
    all_formulas = {}
    latex = []
    for weight in range(2, 13):
        components = symbolic_gaussian(weight)
        all_formulas[str(weight)] = {f'{a},{b}': str(v) for (a,b),v in components.items()}
        latex.append(f'% Weight {weight}: '+('real' if weight%2 else 'imaginary'))
        for (a,b), value in components.items():
            name = 'h' if weight%2 else 'g'
            latex.append(f'{name}_{{{a},{b}}} &= {sp.latex(value)} \\\\')
    (ROOT/'gaussian_parity_through_weight12.json').write_text(json.dumps(all_formulas, indent=2)+'\n')
    (ROOT/'gaussian_parity_through_weight12.tex').write_text('\n'.join(latex)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'checks'}, indent=2))


if __name__ == '__main__':
    main()
