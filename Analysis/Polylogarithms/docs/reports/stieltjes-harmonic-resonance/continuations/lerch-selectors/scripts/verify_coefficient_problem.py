#!/usr/bin/env python3
"""Independent checks for Section 11, using the source's Definition 1.

Exact identities use rational convolution, not fitted values. Numerical
comparisons are diagnostics, not interval error certificates. The two
mutation controls deliberately insert the printed normalization/sign.
"""
from __future__ import annotations
from collections import Counter
import json
from pathlib import Path
import mpmath as mp
import sympy as sp
from selector_algebra import negative_polylog

ROOT = Path(__file__).resolve().parents[1]
COUNTS: Counter[str] = Counter()
DIAGNOSTICS: list[dict[str, str]] = []


def exact(family: str, expression: sp.Expr) -> None:
    if sp.cancel(expression) != 0:
        raise AssertionError(f'{family}: {expression}')
    COUNTS[family] += 1


def convolution(a: list[sp.Expr], b: list[sp.Expr], order: int) -> list[sp.Expr]:
    return [sum(a[j]*b[k-j] for j in range(k+1)) for k in range(order+1)]


def ell_coefficients(v: int, order: int) -> list[sp.Expr]:
    """Coefficients of t^v exp(2t)/prod(exp(t)-j), computed as series."""
    degree = max(0, order-v+1)
    # exp(t)*t/(exp(t)-1) = sum B_k(1)t^k/k!.
    c = [sp.bernoulli(k, 1)/sp.factorial(k) for k in range(degree+1)]
    for j in range(2, v):
        r = [sp.Rational(1, 1-j)]
        for k in range(1, degree+1):
            r.append(-sum(r[k-i]/sp.factorial(i) for i in range(1,k+1))/(1-j))
        c = convolution(c, r, degree)
    return [sp.Integer(0) if k<v-1 else sp.factorial(k)*c[k-v+1]
            for k in range(order+1)]


def continued_integer(v: int, k: int) -> sp.Expr:
    n = v-1
    if k<n:
        return sp.Integer(0)
    if k==n:
        return sp.Integer((-1)**v*n)
    r = k-v
    value = -n*sp.bernoulli(r+1, 1)/(r+1)
    for j in range(2,n+1):
        z = sp.Rational(1,j)
        value += (-1)**(j-1)*sp.binomial(n,j)*negative_polylog(r,z)/z
    return sp.cancel(-sp.rf(-k,v)*value/sp.factorial(n))


def compare(name: str, left: mp.mpf, right: mp.mpf, tolerance: str = '1e-55') -> None:
    absolute = abs(left-right)
    scaled = absolute/max(mp.mpf(1),abs(left),abs(right))
    if scaled >= mp.mpf(tolerance):
        raise AssertionError(f'{name}: {mp.nstr(scaled,20)} >= {tolerance}')
    DIAGNOSTICS.append({'name':name, 'left':mp.nstr(left,45), 'right':mp.nstr(right,45),
                        'absolute_discrepancy':mp.nstr(absolute,12),
                        'scaled_discrepancy':mp.nstr(scaled,12), 'tolerance':tolerance})
    print('PASS', name, mp.nstr(scaled,7), flush=True)


def main() -> None:
    t = sp.Symbol('t')
    for n in range(1,11):
        target = sp.prod(1/(1-t/j) for j in range(1,n+1))
        reduced = sum((-1)**(j-1)*sp.binomial(n,j)/(1-t/j) for j in range(1,n+1))
        exact('All-node rational partial fractions', target-reduced)
        h = [sp.Integer(1)]+[sp.Integer(0)]*20
        for j in range(1,n+1):
            for m in range(1,21):
                h[m] += h[m-1]/j
        for m in range(21):
            formula = sum((-1)**(j-1)*sp.binomial(n,j)/sp.Integer(j)**m
                          for j in range(1,n+1))
            exact('Complete-homogeneous coefficients', h[m]-formula)
    for v in range(2,8):
        values = ell_coefficients(v,12)
        for k, ell in enumerate(values):
            exact('Defining generating series / zeta interpolation', ell-continued_integer(v,k))
    # The incorrect interpolation sign must fail, including at v=2,k=1.
    assert continued_integer(2,1) != -ell_coefficients(2,1)[1]
    COUNTS['Rejected interpolation-sign mutation'] += 1
    # The two alleged Mellin prefactors have ratio ((v-1)!)^2, not one.
    for v in (3,4,5):
        assert sp.factorial(v-1)**2 != 1
        COUNTS['Rejected factorial-normalization mutation'] += 1

    mp.mp.dps = 75
    for v, sv, av in [(3,'1.3','1.25'), (5,'1.7','1.1')]:
        n = v-1; s = mp.mpf(sv); a = mp.mpf(av); order = s+v
        # Convolution computes the source's nested coefficients directly.
        # The constant tail n is summed by Hurwitz zeta; the remaining tail
        # decays geometrically. This is not a partial-fraction implementation.
        h = [mp.mpf(1)]+[mp.mpf(0)]*260
        for j in range(1,n+1):
            for m in range(1,len(h)):
                h[m] += h[m-1]/j
        direct = n*mp.zeta(order,a)+mp.fsum((h[m]-n)/(a+m)**order for m in range(len(h)))
        direct *= -mp.rf(s,v)/mp.factorial(n)
        finite = n*mp.zeta(order,a)+mp.fsum(
            (-1)**(j-1)*mp.binomial(n,j)*mp.lerchphi(mp.mpf(1)/j,order,a)
            for j in range(2,n+1))
        finite *= -mp.rf(s,v)/mp.factorial(n)
        compare(f'Nested coefficient sum / finite Lerch, v={v}',direct,finite)
        def kernel(x: mp.mpf) -> mp.mpf:
            den = -mp.expm1(-x)
            den *= mp.fprod(1-mp.exp(-x)/j for j in range(2,n+1))
            return x**(s+v-1)*mp.exp(-a*x)/den
        integral = -mp.quad(kernel,[0,1,4,mp.inf])/(mp.factorial(n)*mp.gamma(s))
        compare(f'Corrected Mellin / defining series, v={v}',integral,direct)
    s=mp.mpf('1.4'); a=mp.mpf('1.2')
    integral=mp.quad(lambda t:t**(s+1)*mp.exp(-a*t)/(-mp.expm1(-t)),[0,1,4,mp.inf])
    compare('Positive v=2 Mellin identity',integral,mp.gamma(s+2)*mp.zeta(s+2,a))
    # Jet at s=-2, v=3: symmetric Cauchy differentiation avoids multiplying
    # a floating-point zero by the pole of zeta.
    eps=mp.mpf('0.05')
    def continued(z: mp.mpc) -> mp.mpc:
        return -mp.rf(z,3)/2*(2*mp.zeta(z+3)-mp.lerchphi(mp.mpf('.5'),z+3,1))
    deriv = mp.diff(continued,-2,method='quad',radius=eps)
    compare('Canceled-pole first jet, v=3',deriv,3-2*mp.euler+2*mp.log(2),'1e-50')
    report={'status':'PASS', 'sympy_version':sp.__version__, 'mpmath_version':mp.__version__,
            'exact_assertions':sum(COUNTS.values()), 'exact_families':dict(COUNTS),
            'numerical_diagnostics':len(DIAGNOSTICS), 'working_decimal_digits':mp.mp.dps,
            'maximum_scaled_discrepancy':mp.nstr(max(mp.mpf(d['scaled_discrepancy']) for d in DIAGNOSTICS),12),
            'diagnostics':DIAGNOSTICS,
            'scope':'Finite exact checks plus floating-point diagnostics; not interval or formal-proof certificates.'}
    path=ROOT/'results'/'coefficient_problem_checks.json'
    path.write_text(json.dumps(report,indent=2)+'\n')
    print('PASS',sum(COUNTS.values()),'exact assertions and',len(DIAGNOSTICS),'numerical diagnostics',flush=True)

if __name__=='__main__':
    main()
