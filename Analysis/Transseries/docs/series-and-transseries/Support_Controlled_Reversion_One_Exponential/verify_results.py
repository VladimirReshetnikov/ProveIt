#!/usr/bin/env python3
"""Exact regression checks for the accompanying transseries research article.

Requirements: Python 3.10+, sympy, mpmath.
Run: python verify_results.py
This is finite symbolic testing, not a proof-assistant formalization.
"""
from __future__ import annotations
from fractions import Fraction
from pathlib import Path
import csv
import math
import sys
import sympy as sp
import mpmath as mp

OUT = Path(__file__).resolve().parent
L, w = sp.symbols('L w')
CUT = Fraction(4)
Series = dict[Fraction, sp.Expr]
checks: list[str] = []


def clean(a: Series) -> Series:
    out = {}
    for e, c in a.items():
        c = sp.expand(c)
        if e < CUT and c != 0:
            out[e] = c
    return out


def add(a: Series, b: Series) -> Series:
    d = dict(a)
    for e, c in b.items():
        d[e] = d.get(e, sp.S.Zero) + c
    return clean(d)


def scale(a: Series, c: sp.Expr) -> Series:
    return clean({e: c*v for e, v in a.items()})


def mul(a: Series, b: Series) -> Series:
    d: Series = {}
    for e, u in a.items():
        for f, v in b.items():
            if e+f < CUT:
                d[e+f] = d.get(e+f, sp.S.Zero) + u*v
    return clean(d)


def deriv(a: Series) -> Series:
    return clean({e+1: sp.diff(p, L)-sp.Rational(e.numerator,e.denominator)*p
                  for e, p in a.items()})


def compose_correction(a: Series, b: Series) -> Series:
    # This test uses v(a), v(b) >= 0, so four Taylor terms suffice modulo t^4.
    out: Series = {}
    power: Series = {Fraction(0): sp.S.One}
    derivative = dict(a)
    for n in range(4):
        out = add(out, scale(mul(power, derivative), sp.Rational(1, math.factorial(n))))
        power = mul(power, b)
        derivative = deriv(derivative)
    return out


def inverse_unit(u: Series) -> Series:
    assert u.get(Fraction(0)) == 1
    tail = add(u, {Fraction(0): -sp.S.One})
    if not tail:
        return {Fraction(0): sp.S.One}
    assert min(tail) > 0
    out = {Fraction(0): sp.S.One}
    term = dict(out)
    bound = math.ceil(CUT/min(tail))
    for _ in range(1, bound+1):
        term = scale(mul(term, tail), -sp.S.One)
        out = add(out, term)
    return out


def check_hahn() -> None:
    a = {Fraction(0): L, Fraction(1,2): L**2+1, Fraction(2,3): sp.S.One}
    b: Series = {}
    power = {Fraction(0): sp.S.One}
    for r in range(1,5):
        power = mul(power,a)
        term = dict(power)
        for _ in range(r-1):
            term = deriv(term)
        b = add(b, scale(term, sp.Rational((-1)**r, math.factorial(r))))
    residual = add(b, compose_correction(a,b))
    assert not residual, residual
    checks.append('PASS: mixed 1/2, 2/3, logarithmic Hahn Lagrange formula modulo t^4')
    current: Series = {}
    for _ in range(3):
        resid = add(current,compose_correction(a,current))
        slope = add({Fraction(0): sp.S.One},compose_correction(deriv(a),current))
        current = add(current,scale(mul(resid,inverse_unit(slope)),-sp.S.One))
        assert all(6 % e.denominator == 0 for e in current)
    assert not add(current,scale(b,-sp.S.One))
    checks.append('PASS: three Newton steps agree with Lagrange; denominator remains 6')


def check_exponential_model(N: int = 6) -> list[sp.Expr]:
    b = [sp.S.Zero]
    for n in range(1,N+1):
        p = w**(n+1)/(w+1)
        for _ in range(n-1):
            p = sp.cancel(w/(w+1)*sp.diff(p,w)-n*p)
        p = sp.cancel(sp.Rational((-1)**n,math.factorial(n))*p)
        b.append(p)
        pole = sp.cancel(p*(w+1)**(2*n-1)).subs(w,-1)
        odd_df = math.prod(range(1,2*n-2,2))
        assert sp.simplify(pole+sp.Rational(odd_df,math.factorial(n))) == 0
        num,den = sp.fraction(p)
        assert sp.degree(num,w)-sp.degree(den,w) == n
        lead = sp.LC(sp.Poly(num,w))/sp.LC(sp.Poly(den,w))
        assert lead == -sp.Rational(n**(n-1),math.factorial(n))
    checks.append(f'PASS: exact pole order, pole coefficient, and Cayley leading term for n=1..{N}')
    # Cached powers of delta=sum b_n z^n, truncated at z^(N+1).
    powers = [[sp.S.Zero]*(N+1) for _ in range(N+1)]
    powers[0][0] = sp.S.One
    for j in range(1,N+1):
        for k in range(j,N+1):
            powers[j][k] = sp.cancel(sum(powers[j-1][i]*b[k-i]
                                       for i in range(j-1,k)))
    for k in range(1,N+1):
        logc = sum(sp.Rational((-1)**(j+1),j)*powers[j][k]/w**j
                   for j in range(1,k+1))
        expc = sum(sp.Rational((-1)**j,math.factorial(j))*powers[j][k-1]
                   for j in range(0,k))
        assert sp.cancel(b[k]+logc+w*expc) == 0
    checks.append(f'PASS: implicit equation delta+log(1+delta/w)+w*z*exp(-delta)=0 through z^{N}')
    return b


def numeric_checks(b: list[sp.Expr]) -> None:
    mp.mp.dps = 100
    funcs = [None]+[sp.lambdify(w,p,'mpmath') for p in b[1:]]
    rows=[]
    for ww in (4,5,8,12):
        W=mp.mpf(ww)
        x=W+mp.log(W)
        q=mp.exp(-x)
        delta=mp.findroot(lambda d: d+mp.log1p(d/W)+W*q*mp.exp(-d),(-2*W*q,mp.mpf('0')))
        partial=mp.mpf('0')
        theta=16*mp.exp(-W)
        for n in range(1,len(b)):
            partial += funcs[n](W)*q**n
            error=abs(delta-partial)
            bound=theta**(n+1)/(4*(1-theta))
            assert error <= bound
            rows.append({'w':ww,'N':n,'x':mp.nstr(x,32),
                         'inverse_value':mp.nstr(W+delta,45),
                         'absolute_error':mp.nstr(error,14),
                         'proved_bound':mp.nstr(bound,14)})
    with (OUT/'numeric_checks.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]))
        writer.writeheader();writer.writerows(rows)
    checks.append('PASS: 100-digit numerical tests at w=4,5,8,12 and N=1..6 satisfy the proved bound')


def main() -> None:
    check_hahn()
    b=check_exponential_model()
    numeric_checks(b)
    report=['Verification report', 'Exact symbolic checks plus non-interval numerical regression tests.',
            f'Python {sys.version.split()[0]}; SymPy {sp.__version__}; mpmath {mp.__version__}', '']
    report += checks
    report += ['', 'Coefficients for X+log(X)+exp(-X):']
    report += [f'b_{n}(w) = {sp.factor(b[n])}' for n in range(1,len(b))]
    report += ['', 'These finite checks do not replace the proofs in the article.',
               'No Lean, Coq, or other proof-assistant verification is claimed.']
    text='\n'.join(report)+'\n'
    (OUT/'verification_report.txt').write_text(text)
    print(text)

if __name__ == '__main__':
    main()
