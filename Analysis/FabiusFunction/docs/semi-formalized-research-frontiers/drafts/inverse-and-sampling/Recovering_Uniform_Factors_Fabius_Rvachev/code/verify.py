#!/usr/bin/env python3
"""Reproduce exact certificates and numerical diagnostics for the article.

Exact rational checks support finite polynomial identities. Floating-point
checks are diagnostics, not interval certificates and not proofs of the
all-n analytic estimates. Run from any directory; results go to ../data.
Dependencies: sympy, mpmath. No network access is used.
"""
from __future__ import annotations
import json
import math
import platform
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
import sympy as sp

OUT = Path(__file__).resolve().parents[1] / 'data'
OUT.mkdir(exist_ok=True)


def chebyshev_coefficients(n: int) -> list[int]:
    """T_n in ascending powers, computed entirely with integers."""
    if n < 0:
        raise ValueError('n must be nonnegative')
    a, b = [1], [0, 1]
    if n == 0:
        return a
    for _ in range(1, n):
        c = [0] + [2*v for v in b]
        for j, v in enumerate(a):
            c[j] -= v
        a, b = b, c
    return b


def root_powers(coeff: list[F], upto: int) -> list[F]:
    """Power sums of roots of a monic polynomial, by Newton identities."""
    n = len(coeff)-1
    assert coeff[-1] == 1
    c = list(reversed(coeff))  # z^n + c[1]z^(n-1)+...+c[n]
    p = [F(n)]
    for k in range(1, upto+1):
        if k <= n:
            p.append(-sum((c[j]*p[k-j] for j in range(1,k)), F(0))-k*c[k])
        else:
            p.append(-sum((c[j]*p[k-j] for j in range(1,n+1)), F(0)))
    return p


def shifted_powers(p: list[F], shift: int) -> list[F]:
    return [sum((F(math.comb(k,j))*shift**(k-j)*p[j]
                 for j in range(k+1)), F(0)) for k in range(len(p))]


def roots(n: int, sign: int) -> list[mp.mpf]:
    if n < 2 or sign not in (-1,1):
        raise ValueError('n >= 2 and sign in {-1,1} required')
    alpha = mp.acos(mp.mpf(sign)/2)
    def angle(j: int) -> mp.mpf:
        return (2*mp.pi*((j+1)//2) + (alpha if j % 2 == 0 else -alpha))/n
    return [mp.cos(angle(j)) for j in range(n)]


def sinc(t: mp.mpf) -> mp.mpf:
    return mp.sin(t)/t if t else mp.mpf(1)


def dsinc(t: mp.mpf) -> mp.mpf:
    return (t*mp.cos(t)-mp.sin(t))/t**2 if t else mp.mpf(0)


def characteristic_and_derivative(n: int, sign: int, t: mp.mpf):
    widths = [mp.sqrt(3+y) for y in roots(n, sign)] + [mp.mpf(1)]*(2*n)
    factors = [sinc(a*t) for a in widths]
    prod = mp.fprod(factors)
    # Product rule avoids division by a potentially vanishing sinc factor.
    derivative = mp.fsum(a*dsinc(a*t)*mp.fprod(factors[:i]+factors[i+1:])
                         for i,a in enumerate(widths))
    return prod, derivative


def main() -> None:
    exact_equalities = 0
    leading_defects = 0
    for n in range(2,81):
        base = [F(v, 2**(n-1)) for v in chebyshev_coefficients(n)]
        plus, minus = base.copy(), base.copy()
        plus[0] -= F(1,2**n)
        minus[0] += F(1,2**n)
        yp, ym = root_powers(plus,n), root_powers(minus,n)
        xp, xm = shifted_powers(yp,3), shifted_powers(ym,3)
        for k in range(1,n):
            assert yp[k] == ym[k]
            assert xp[k] == xm[k]
            exact_equalities += 2
        assert yp[n]-ym[n] == F(n,2**(n-1))
        assert xp[n]-xm[n] == F(n,2**(n-1))
        assert xp[1] == 3*n and xm[1] == 3*n
        leading_defects += 2

    cumulant_checks = 0
    for n in range(2,41):
        eta = sp.Rational(1, 2**((n-1).bit_length()+1))
        defect = (sp.Rational(2**(2*n),2*n)*sp.bernoulli(2*n)
                  *eta**(2*n)*sp.Rational(n,2**(n-1)))
        assert sp.cancel(defect-2**n*sp.bernoulli(2*n)*eta**(2*n)) == 0
        cumulant_checks += 1

    rank_checks = []
    for m in range(1,9):
        a = [sp.Rational(1,2**j) for j in range(1,m+3)]
        rows = [[sp.Integer(1)]*len(a)]
        rows += [[2*k*x**(2*k-1) for x in a] for k in range(1,m+1)]
        J = sp.Matrix(rows)
        Jnext = sp.Matrix(rows+[[2*(m+1)*x**(2*m+1) for x in a]])
        assert J.rank() == m+1
        assert Jnext.det() != 0
        rank_checks.append({'M':m, 'rank':m+1, 'augmented_invertible':True})

    th = sp.symbols('theta', real=True)
    av = [(7+u*sp.cos(th)+sp.sqrt(3)*v*sp.sin(th))/24
          for u,v in zip([5,-1,-4],[-1,3,-2])]
    assert sp.trigsimp(sum(av)-sp.Rational(7,8)) == 0
    assert sp.trigsimp(sum(x*x for x in av)-sp.Rational(21,64)) == 0
    kappa4_derivative = sp.simplify(-sp.Rational(2,15)*sum(
        sp.diff(x**4,th).subs(th,0) for x in av))
    assert kappa4_derivative == 7*sp.sqrt(3)/3840

    mp.mp.dps = 90
    numeric_root_checks = 0
    numeric_gap_checks = 0
    for n in range(2,101):
        for sign in (-1,1):
            for y in roots(n,sign):
                residual = abs(mp.cos(n*mp.acos(y))-mp.mpf(sign)/2)
                assert residual < mp.mpf('1e-80')
                numeric_root_checks += 1
        eta = mp.mpf(2)**(-((n-1).bit_length()+1))
        j = (n-1)//2
        gap = eta*abs(mp.sqrt(3+roots(n,1)[j])-mp.sqrt(3+roots(n,-1)[j]))
        assert gap >= mp.mpf(1)/(48*n**2)
        numeric_gap_checks += 1

    fourier_checks = 0
    q = 4/mp.pi**2
    for n in range(2,11):
        for j in range(1,21):
            t = mp.mpf(j)/20
            p,dp = characteristic_and_derivative(n,1,t)
            m,dm = characteristic_and_derivative(n,-1,t)
            assert abs(p-m) <= 8*q**n*t**(2*n)
            assert abs(dp-dm) <= 64*n*q**n*t**(2*n-1)
            fourier_checks += 2

    table = []
    for n in [16,32,64,128,256]:
        eta = mp.mpf(2)**(-((n-1).bit_length()+1))
        j = (n-1)//2
        gap = eta*abs(mp.sqrt(3+roots(n,1)[j])-mp.sqrt(3+roots(n,-1)[j]))
        c = 1/mp.sqrt(1+15*n*eta**2)
        eps = min(mp.mpf(1),40*n*(mp.mpf(6)/7)**(2*n-1))
        table.append({'n':n, 'eta':str(eta),
                      'displayed_coordinate_gap':mp.nstr(gap,14),
                      'normalized_coordinate_gap':mp.nstr(c*gap,14),
                      'proved_TV_upper_bound':mp.nstr(eps,14),
                      'proved_gap_lower_bound':mp.nstr(mp.mpf(1)/(48*n**2),14)})

    result = {'status':'PASS',
        'exact_power_sum_equalities':exact_equalities,
        'exact_leading_power_sum_defects':leading_defects,
        'exact_cumulant_defects':cumulant_checks,
        'exact_Jacobian_checks':rank_checks,
        'explicit_curve_invariants':'PASS',
        'explicit_curve_kappa4_derivative':str(kappa4_derivative),
        'numerical_root_residual_checks':numeric_root_checks,
        'numerical_gap_checks':numeric_gap_checks,
        'numerical_Fourier_inequality_checks':fourier_checks,
        'numeric_precision_decimal_digits':mp.mp.dps,
        'table':table,
        'environment':{'python':platform.python_version(),'sympy':sp.__version__,
                       'mpmath':mp.__version__},
        'limits':'Finite tests do not prove the all-n claims. Numeric tests are not interval-certified. No Lean proof is supplied.'}
    (OUT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    (OUT/'verification.txt').write_text(
        'PASS\nExact power-sum equalities: '+str(exact_equalities)+
        '\nExact leading defects: '+str(leading_defects)+
        '\nExact cumulant defects: '+str(cumulant_checks)+
        '\nJacobian rank / determinant cases: 8 each\nExplicit isomoment curve: PASS\n'+
        '90-digit diagnostics: '+str(numeric_root_checks)+' root residuals, '+
        str(numeric_gap_checks)+' gaps, '+str(fourier_checks)+' Fourier inequalities.\n'+
        result['limits']+'\n')
    rows = ['% Generated by code/verify.py; TV entries are analytic upper bounds.']
    for row in table:
        def tex_sci(v):
            x = mp.mpf(v)
            if x == 1: return '1'
            e = int(mp.floor(mp.log10(abs(x))))
            return mp.nstr(x/10**e,4)+r'\times 10^{'+str(e)+'}'
        rows.append(f"{row['n']} & ${tex_sci(row['displayed_coordinate_gap'])}$ & "
                    f"${tex_sci(row['normalized_coordinate_gap'])}$ & "
                    f"${tex_sci(row['proved_TV_upper_bound'])}$ " + chr(92)*2)
    (OUT/'table_rows.tex').write_text('\n'.join(rows)+'\n')
    print((OUT/'verification.txt').read_text())
    print(json.dumps(table,indent=2))

if __name__ == '__main__':
    main()
