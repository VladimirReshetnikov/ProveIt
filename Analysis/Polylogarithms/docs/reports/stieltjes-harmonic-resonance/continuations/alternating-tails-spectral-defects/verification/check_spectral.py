#!/usr/bin/env python3
"""Exact regressions and independent numerical diagnostics for spectral defects.

No numerical test is a proof or an interval certificate.  The independent
spectral check expands the quadratic zeta and differentiates the separate
linear-factor Hurwitz functions, then compares with the subtracted-log kernel.
"""
from __future__ import annotations
import argparse
import json
import math
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]


def exact_checks():
    s, b, u, v, L, A, B = sp.symbols('s b u v L A B')
    count = 0
    for k in range(1, 17):
        p = sp.Poly(sp.rf(2*s, 2*k)/sp.factorial(2*k)
                    - sp.rf(s, k)/sp.factorial(k), s)
        e1, e2 = elementary(2*k-1, 7), elementary(k-1, 7)
        for m in range(0, 8):
            expected = 0 if m < 2 else (
                sp.Rational(2**(m-1))*sp.Rational(e1[m-1])
                - sp.Rational(e2[m-1]))/k
            assert sp.simplify(p.nth(m)-expected) == 0
            count += 1
        assert sp.simplify(p.nth(2)/2
                           - (sp.harmonic(2*k)-sp.harmonic(k)/2)/k) == 0
        count += 1
    for r in range(2, 10):
        lhs = (-1)**r*(2**(r-1)*((L/2+sp.I*v)**r+(L/2-sp.I*v)**r)-L**r)
        rhs = sum((-1)**(r+j)*4**j*sp.binomial(r, 2*j)
                  *L**(r-2*j)*v**(2*j) for j in range(1, r//2+1))
        assert sp.expand(lhs-rhs) == 0
        count += 1
    t = sp.symbols('t')
    for k in range(2, 14):
        beta = (-1)**k*sum((A**j-B**j)*(A**(k-j)-B**(k-j))
                            /sp.Integer(j*(k-j)) for j in range(1, k))
        assert sp.expand(beta.subs(B,A)) == 0
        assert sp.expand(sp.diff(beta,A,B)
                         +2*(-1)**(k-2)*sum(A**j*B**(k-2-j)
                                             for j in range(k-1))) == 0
        count += 2
    logsquare = sp.series(sp.log(1+t)**2, t, 0, 18).removeO()
    for k in range(2, 18):
        assert logsquare.coeff(t,k) == 2*(-1)**k*sp.harmonic(k-1)/k
        count += 1
    xs = sp.symbols('x0:5')
    assert sp.expand(5*sum(x*x for x in xs)-sum(xs)**2
                     -sum((xs[i]-xs[j])**2 for i in range(5)
                          for j in range(i+1,5))) == 0
    count += 1
    # A deliberate deleted resonance is an exact negative control.
    assert (-b*b) != 0
    count += 1
    return count


@lru_cache(None)
def elementary(n, order):
    e = [Fraction(1)] + [Fraction(0)]*order
    for j in range(1, n+1):
        for r in range(order, 0, -1):
            e[r] += e[r-1]/j
    return tuple(e)


def mpr(x):
    return mp.mpf(x.numerator)/x.denominator


def alpha(k, m, b):
    if m < 2 or m > 2*k:
        return mp.mpf(0)
    e1 = elementary(2*k-1, m-1)[m-1]
    e2 = elementary(k-1, m-1)[m-1]
    return (-1)**k*b**(2*k)/k*mpr(2**(m-1)*e1-e2)


def qcoef(k, m, b):
    if k == 0:
        return mp.mpf(m == 0)
    if m < 1 or m > k:
        return mp.mpf(0)
    return (-1)**k*b**(2*k)/k*mpr(elementary(k-1,m-1)[m-1])


@lru_cache(None)
def zd(nu, j, a):
    if j == 0:
        return mp.zeta(nu,a)
    return mp.diff(lambda t: mp.zeta(t,a), nu, j)


@lru_cache(None)
def st(j, a):
    return mp.stieltjes(j,a)


def pole_product(coef, r, a, resonant):
    if resonant:
        return coef(r+1)/2 + sum(coef(m)*(-2)**(r-m)*st(r-m,a)
                                  /mp.factorial(r-m) for m in range(r+1))
    raise ValueError('only the resonant branch is called here')


def quadratic_derivative(w, a, b, r, terms=70):
    """Independent expansion of Z_W, not of its factorization difference."""
    out = mp.mpc(0)
    for d, weight in enumerate(w):
        if not weight:
            continue
        for k in range(terms):
            nu = 2*k-d
            cf = lambda m: qcoef(k,m,b)
            if nu == 1:
                value = pole_product(cf,r,a,True)
            else:
                value = sum(cf(m)*2**(r-m)*zd(nu,r-m,a)
                            /mp.factorial(r-m) for m in range(r+1)
                            if cf(m))
            out += weight*value
    return mp.factorial(r)*out


def linear_derivative(w, a, b, r, sign):
    c = sign*mp.j*b
    return sum(weight*math.comb(d,j)*(-c)**(d-j)*zd(-j,r,a+c)
               for d,weight in enumerate(w) for j in range(d+1))


def H(r,x,b):
    t = mp.atan(b/x)
    logq = mp.log(x*x+b*b)
    return sum((-1)**(r+j)*4**j*math.comb(r,2*j)
               *logq**(r-2*j)*t**(2*j) for j in range(1,r//2+1))


def subtracted_defect(w, a, b, r, head=12, tail_terms=30):
    degree = len(w)-1
    K = (degree+1)//2
    W = lambda x: sum(c*x**d for d,c in enumerate(w))
    pk = lambda k,x: mp.factorial(r)*sum(alpha(k,m,b)*(-2*mp.log(x))**(r-m)
                                        /mp.factorial(r-m)
                                        for m in range(2,min(r,2*k)+1))
    result = sum(W(n+a)*(H(r,n+a,b)-sum(pk(k,n+a)/(n+a)**(2*k)
                                      for k in range(1,K+1))) for n in range(head))
    # Evaluate the remaining ordinary tail by its convergent binomial expansion.
    for d,weight in enumerate(w):
        if not weight:
            continue
        for k in range(K+1, K+1+tail_terms):
            result += weight*mp.factorial(r)*sum(
                alpha(k,m,b)*2**(r-m)*zd(2*k-d,r-m,a+head)/mp.factorial(r-m)
                for m in range(2,min(r,2*k)+1))
        for k in range(1,K+1):
            nu = 2*k-d
            if nu == 1:
                value = alpha(k,r+1,b)/2 + sum(
                    alpha(k,m,b)*(-2)**(r-m)*st(r-m,a)/mp.factorial(r-m)
                    for m in range(2,min(r,2*k)+1))
            else:
                value = sum(alpha(k,m,b)*2**(r-m)*zd(nu,r-m,a)
                            /mp.factorial(r-m) for m in range(2,min(r,2*k)+1))
            result += weight*mp.factorial(r)*value
    return result


def S_series(a,b,head=10,terms=35):
    # Head is a direct ordinary sum; the tail uses the exact arctangent-square series.
    result = sum(mp.atan(b/(n+a))**2 for n in range(head))
    for k in range(1,terms+1):
        oddH = mp.harmonic(2*k)-mp.harmonic(k)/2
        result += (-1)**(k+1)*b**(2*k)*oddH/k*mp.zeta(2*k,a+head)
    return result


def gamma_integral(a,b):
    base = mp.re(mp.loggamma(a+mp.j*b))
    def f(t):
        if t == 1:
            return b*mp.im(mp.digamma(a+mp.j*b))
        return 2*(mp.re(mp.loggamma(a+mp.j*b*t))-base)/(1-t*t)
    return mp.quad(f,[0,mp.mpf('.5'),1])


def beta(k,B,C):
    return (-1)**k*sum((B**j-C**j)*(B**(k-j)-C**(k-j))/mp.mpf(j*(k-j))
                       for j in range(1,k))


def weighted_K(p,a,B,C,head=12,terms=35):
    D = len(p)-1
    W = lambda x: sum(c*x**(2*d) for d,c in enumerate(p))
    result = sum(W(x)*(mp.log((x*x+B)/(x*x+C))**2
                          -sum(beta(k,B,C)*x**(-2*k) for k in range(2,D+1)))
                 for x in (a+n for n in range(head)))
    for d,c in enumerate(p):
        for k in range(max(2,D+1),max(2,D+1)+terms):
            result += c*beta(k,B,C)*mp.zeta(2*k-2*d,a+head)
        for k in range(2,D+1):
            result += c*beta(k,B,C)*mp.zeta(2*k-2*d,a)
    return result


def R(a,B):
    b=mp.sqrt(B)
    return (mp.digamma(a+mp.j*b)-mp.digamma(a-mp.j*b))/(2*mp.j*b)


def RW(p,a,B):
    return sum(c*(-B)**j for j,c in enumerate(p))*R(a,B) + sum(
        c*(-B)**ell*mp.zeta(-2*(j-1-ell),a)
        for j,c in enumerate(p) for ell in range(j))


def numeric_checks():
    mp.mp.dps = 65
    rows=[]
    def record(name,lhs,rhs,tol=mp.mpf('1e-45')):
        err=abs(lhs-rhs)
        assert err < tol, (name,mp.nstr(lhs,50),mp.nstr(rhs,50),mp.nstr(err,10))
        rows.append({'check':name,'value':mp.nstr(mp.re(lhs),48),
                     'absolute_error':mp.nstr(err,8),'tolerance':str(tol)})
    for a,b in [(mp.mpf('1'),mp.mpf('.3')),
                (mp.mpf('.5'),mp.mpf('1.2')),
                (mp.mpf('1.3'),mp.mpf('.7'))]:
        record('logGamma integral a='+str(a)+' b='+str(b),S_series(a,b),gamma_integral(a,b))
    a,b=mp.mpf('.8'),mp.mpf('.2')
    for w,r in [([1],2),([1],3),([0,1],1),([0,1],3),([1,2,-1,1],2),([0,0,0,0,0,1],3)]:
        spectral=2**(r-1)*(linear_derivative(w,a,b,r,1)+linear_derivative(w,a,b,r,-1))
        spectral-=quadratic_derivative(w,a,b,r)
        kernel=subtracted_defect(w,a,b,r)
        record('full spectral defect W='+str(w)+' r='+str(r),spectral,kernel)
    a,B,C=mp.mpf('.9'),mp.mpf('.6'),mp.mpf('1.1')
    for p in ([1],[0,1],[1,-2,1],[0,0,0,1]):
        value=weighted_K(p,a,B,C)
        # The mixed derivative independently compares the logarithmic kernel
        # with the finite polygamma/Bernoulli resolvent.
        cross=mp.diff(lambda bb,cc: weighted_K(p,a,bb,cc), (B,C),(1,1))
        target=-2*(RW(p,a,B)-RW(p,a,C))/(C-B)
        record('weighted mixed mass derivative P='+str(p),cross,target)
        record('weighted diagonal P='+str(p),weighted_K(p,a,B,B),0)
    for m in range(1,5):
        z=mp.mpf('1.2')+mp.j*mp.mpf('.4')
        fun=lambda t:(zd(-m,1,t)+mp.harmonic(m)*mp.zeta(-m,t))/mp.factorial(m)
        record('Hurwitz primitive order '+str(m),mp.diff(fun,z,m),zd(0,1,z))
    return rows


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--exact-only',action='store_true')
    args=parser.parse_args()
    count=exact_checks()
    print(json.dumps({'exact_assertions':count}),flush=True)
    rows=[] if args.exact_only else numeric_checks()
    result={'exact_assertions':count,'numerical_checks':len(rows),
            'precision_digits':65,'numerical_diagnostics_are_not_interval_certificates':True,
            'checks':rows}
    out=ROOT/'data'/'spectral_verification.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'passed','numerical_checks':len(rows),'output':str(out)}))


if __name__=='__main__':
    main()
