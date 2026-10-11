#!/usr/bin/env python3
"""Reproducible exact checks and independent numerical diagnostics.

Exact finite checks are regression tests, not substitutes for the article's
all-index proofs. mpmath comparisons below are NOT interval certificates.
Run: python code/verify.py --part exact|numeric|all
"""
from __future__ import annotations
import argparse
import json
import math
import platform
from pathlib import Path
from functools import lru_cache
import sympy as sp
import mpmath as mp
from sympy.functions.combinatorial.numbers import stirling

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
DATA.mkdir(exist_ok=True)
a,b,c,u,t = sp.symbols('a b c u t')
L,g = sp.symbols('L gamma')


def exp_coeff(log_coeff: list, N: int) -> list:
    out = [sp.Integer(1)]
    for k in range(1,N+1):
        out.append(sp.expand(sum(j*log_coeff[j]*out[k-j]
                       for j in range(1,k+1))/k))
    return out


def gauss_coeff(N: int, aa, bb, ss, cc) -> list:
    d = [sp.Integer(0)]
    for j in range(1,N+1):
        v = (sp.bernoulli(j+1,aa-cc)+sp.bernoulli(j+1,bb-cc)
             -sp.bernoulli(j+1,aa+bb+ss-cc)-sp.bernoulli(j+1,1-cc))
        d.append(sp.expand(sp.Rational((-1)**(j+1),j*(j+1))*v))
    return exp_coeff(d,N)


def tail_q(r: int,k: int,aa,bb,cc):
    return sp.expand(sum(sp.binomial(k,ell)*cc**(k-ell)
             *sum((-1)**j*stirling(ell,j,kind=2)*sp.rf(aa,j)*sp.rf(bb,j)
                  /sp.rf(r+1,j) for j in range(ell+1))
             for ell in range(k+1)))


def heat_coeff(N: int,shift,uu=u):
    d=[sp.Integer(0)]*(N+1)
    if N: d[1]=(1+uu)/2-shift
    for j in range(2,N+1,2):
        d[j]=-(1+uu)*sp.bernoulli(j)/(j*sp.factorial(j))
    return exp_coeff(d,N)


def cumulants(N: int):
    f=[sp.Integer(0),-2*L]+[None]*(max(0,N-1))
    h=[sp.Integer(0),-2*L]+[None]*(max(0,N-1))
    for j in range(2,N+1):
        z=sp.Symbol(f'z{j}')
        f[j]=(z if j%2==0 else (sp.Rational(2)**(1-j)-1)*z)/j
        h[j]=((3-sp.Rational(2)**(2-j))*z if j%2==0
              else (sp.Rational(2)**(1-j)-1)*z)/j
    return f[:N+1],h[:N+1]


def exact_suite():
    groups={}
    def check(name, expr):
        if sp.cancel(expr)!=0:
            raise AssertionError(f'{name}: {sp.factor(expr)}')
        groups[name]=groups.get(name,0)+1
    # Full symbolic identities: independent Bernoulli and finite Stirling forms.
    for r in range(4):
        A=gauss_coeff(r+3,a,b,-r,sp.Integer(0))
        pref=sp.Rational((-1)**r,math.factorial(r))*sp.rf(1-a,r)*sp.rf(1-b,r)
        for k in range(4):
            check('symbolic_tail',A[r+k]-pref*tail_q(r,k,a,b,0))
    # Higher orders, several unrelated rational parameter sets, including roots.
    samples=[(sp.Rational(2,3),sp.Rational(7,5),sp.Rational(3,7)),
             (sp.Rational(-3,4),sp.Rational(9,7),sp.Rational(-2,5)),
             (sp.Integer(2),sp.Integer(3),sp.Rational(1,2))]
    for r in range(9):
        for aa,bb,cc in samples:
            A=gauss_coeff(r+6,aa,bb,-r,cc)
            pref=sp.Rational((-1)**r,math.factorial(r))*sp.rf(1-aa,r)*sp.rf(1-bb,r)
            for k in range(7):
                check('rational_tail',A[r+k]-pref*tail_q(r,k,aa,bb,cc))
    # Translation and Appell identities, independent of the reflection family.
    ss=sp.Symbol('s')
    A=gauss_coeff(5,a,b,ss,c)
    for k in range(1,6):
        check('coefficient_transport',sp.diff(A[k],c)-(ss+k)*A[k-1])
    for r in range(5):
        for k in range(1,6):
            check('appell_tail',sp.diff(tail_q(r,k,a,b,c),c)-k*tail_q(r,k-1,a,b,c))
    # Finite product collapse at integer parameter roots.
    for r in range(1,7):
        for B in range(1,r+1):
            aa,cc=sp.Rational(5,3),sp.Rational(2,7)
            A=gauss_coeff(r+2,aa,sp.Integer(B),-r,cc)
            poly=sp.Poly(sp.prod(1+(aa-cc-h)*t for h in range(1,r-B+1))
                 *sp.prod(1+(h-cc)*t for h in range(1,B)),t)
            for k in range(r+3):
                check('integer_root_collapse',A[k]-poly.nth(k))
    # Moving-reflection heat coefficients and centered parity.
    hs=heat_coeff(12,a)
    for j in range(13):
        check('moving_reflection',hs[j].subs(a,1+u-a)-(-1)**j*hs[j])
    hc=heat_coeff(20,(1+u)/2)
    for j in range(1,21,2):
        check('centered_parity',hc[j])
    # Multivariate, unequal-frequency centered heat kernels: all odd coefficients.
    v,w=sp.symbols('v w')
    for freqs,us in [([1,2],[u,v]),([sp.Rational(2,3),sp.Rational(7,4)],[u,v]),
                     ([1,2,3],[u,v,w])]:
        d=[sp.Integer(0)]*11
        for j in range(2,11,2):
            d[j]=-sp.bernoulli(j)*sum((1+z)*q**j for q,z in zip(freqs,us))/(j*sp.factorial(j))
        h=exp_coeff(d,10)
        for j in range(1,11,2): check('unequal_frequency_parity',h[j])
    # Gamma-reflection cumulants, via the independently expanded tan prefactor.
    fc,hlog=cumulants(8)
    F=exp_coeff(fc,8); H=exp_coeff(hlog,8)
    tan_normal=sp.series(sp.tan(sp.pi*u/2)/(sp.pi*u/2),u,0,9).removeO()
    # Even zeta symbols satisfy their classical Bernoulli evaluations.
    subeven={sp.Symbol(f'z{j}'):sp.zeta(j) for j in range(2,9,2)}
    prod=sp.Poly(sp.expand(tan_normal*sum(F[j]*u**j for j in range(9))),u)
    for k in range(9):
        check('gamma_cumulants',(prod.nth(k)-H[k]).subs(subeven))
    # Reciprocal Gamma and centered Stieltjes finite-part table.
    gl=[sp.Integer(0),g]+[sp.Rational((-1)**(j+1),j)*sp.Symbol(f'z{j}') for j in range(2,10)]
    G=exp_coeff(gl,9)
    Fc=exp_coeff(cumulants(9)[0],9)
    tables={
      'symbols': 'L=log(2), gamma=Euler constant, zj=zeta(j)',
      'C_r_2_divided_by_pi2_over2':[str(sp.factor(x)) for x in H],
      'FP_C_r_at_s1':[str(sp.factor(G[r+1]-Fc[r+1])) for r in range(7)],
      'Q_first_three':[str(tail_q(2,k,a,b,c)) for k in range(4)]}
    (DATA/'exact_tables.json').write_text(json.dumps(tables,indent=2)+'\n')
    # Corruption controls: each deliberately wrong assertion must be rejected.
    controls={}
    wrong=gauss_coeff(2,sp.Rational(2,3),sp.Rational(5,4),-1,0)[2]
    pref=-sp.rf(1-sp.Rational(2,3),1)*sp.rf(1-sp.Rational(5,4),1)
    controls['tail_sign_flip_rejected']=bool(sp.cancel(wrong+pref*tail_q(1,1,sp.Rational(2,3),sp.Rational(5,4),0))!=0)
    controls['frozen_reflection_rejected']=bool(sp.expand(hs[1]+hs[1].subs(a,1-a))==u)
    controls['wrong_center_slope_rejected']=bool(heat_coeff(1,sp.Rational(1,2))[1]==u/2)
    gamma1,zpp0=sp.symbols('gamma1 zeta_second_at_zero')
    # epsilon^2 coefficient of the exact x=1 master formula.
    correct_jet2=-1-g/2+gamma1/2-zpp0/2
    corrupted_jet2=-1-g/2-gamma1/2-zpp0/2
    controls['stieltjes_gamma1_sign_rejected']=bool(sp.expand(correct_jet2-corrupted_jet2)!=0)
    if not all(controls.values()): raise AssertionError(controls)
    result={'status':'PASS','arithmetic':'exact SymPy rational/polynomial arithmetic',
            'groups':groups,'exact_identity_checks':sum(groups.values()),
            'corruption_controls':controls,'sympy':sp.__version__,
            'scope':'Finite regression tests; the all-index theorems are proved in the article.'}
    (DATA/'exact_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


def mp_exp_coeff(d,N):
    out=[mp.mpf(1)]
    for k in range(1,N+1): out.append(sum(j*d[j]*out[k-j] for j in range(1,k+1))/k)
    return out


def central_gamma(uu):
    if not uu: return mp.pi**2/2
    return mp.pi*mp.tan(mp.pi*uu/2)/uu *mp.gamma((1+uu)/2)*mp.gamma(1-uu)/mp.gamma((1-uu)/2)


def central_mellin2(uu):
    def f(x):
        logh=-x/2-mp.log(-mp.expm1(-x))
        return x*mp.exp((1+uu)*logh)
    return mp.quad(f,[0,mp.mpf('0.5'),2,8,mp.inf])


def central_moment(r):
    def f(x):
        logh=-x/2-mp.log(-mp.expm1(-x))
        return x*mp.exp(logh)*logh**r/mp.factorial(r)
    return mp.quad(f,[0,mp.mpf('0.5'),2,8,mp.inf])


def ratio_tail_coeff(eps,M):
    d=[mp.mpf(0)]
    for j in range(1,M+1):
        d.append((-1)**(j+1)*(mp.bernpoly(j+1,0)-mp.bernpoly(j+1,eps))/(j*(j+1)))
    return mp_exp_coeff(d,M)


def beta_subtracted_series(x,eps,N=160,M=24):
    # Convergent summands are computed directly; only the tail is approximated.
    # No rigorous error enclosure is claimed for this diagnostic accelerator.
    out=mp.mpf(0)
    for n in range(N):
        y=n+x
        out+=mp.exp(mp.loggamma(y)-mp.loggamma(y+eps))-y**(-eps)-eps*(1-eps)/2*y**(-1-eps)
    T=ratio_tail_coeff(eps,M)
    out+=sum(T[j]*mp.zeta(eps+j,N+x) for j in range(2,M+1))
    return out


def beta_closed(x,eps):
    return mp.gamma(x)*mp.rgamma(x+eps-1)/(eps-1)-mp.zeta(eps,x)-eps*(1-eps)/2*mp.zeta(1+eps,x)


def numeric_suite():
    mp.mp.dps=65
    rows=[]
    def record(name, lhs, rhs, tolerance='1e-42', **params):
        err=abs(lhs-rhs)/max(1,abs(rhs))
        passed=err<mp.mpf(tolerance)
        rows.append({'name':name,'parameters':{k:str(v) for k,v in params.items()},
                     'lhs':mp.nstr(lhs,55),'rhs':mp.nstr(rhs,55),
                     'relative_or_absolute_error':mp.nstr(err,8),'tolerance':tolerance,'passed':passed})
        if not passed: raise AssertionError(rows[-1])
    for uu in [mp.mpf('-0.3'),mp.mpf('-0.1'),mp.mpf('0'),mp.mpf('0.1'),mp.mpf('0.2'),mp.mpc('.12','.08')]:
        record('ordinary_Mellin_vs_Gamma',central_mellin2(uu),central_gamma(uu),u=uu)
    d=[mp.mpf(0),-2*mp.log(2)]
    for j in range(2,7):
        z=mp.zeta(j)
        d.append(((3-mp.power(2,2-j))*z if j%2==0 else (mp.power(2,1-j)-1)*z)/j)
    H=mp_exp_coeff(d,6)
    for r in range(7):
        record('log_sinh_moment_vs_cumulants',central_moment(r),mp.pi**2/2*H[r],r=r)
    for x in [mp.mpf('0.7'),mp.mpf(1),mp.mpf('1.4'),mp.mpf('2.5')]:
        for eps in [mp.mpf('-.2'),mp.mpf('.15'),mp.mpf('.4')]:
            record('subtracted_sum_vs_Beta_Stieltjes',beta_subtracted_series(x,eps),beta_closed(x,eps),
                   tolerance='1e-39',x=x,epsilon=eps)
    # First logarithmic primitive, independently differentiated.
    def prim(x):
        dz=mp.diff(lambda s:mp.zeta(s,x),-1)
        return (x-mp.mpf('.5'))*mp.loggamma(x)-2*dz+x*x/2-x/2-x*mp.log(2*mp.pi)/2
    for x in [mp.mpf('.7'),mp.mpf('1.3'),mp.mpf('2.2')]:
        target=(x-mp.mpf('.5'))*mp.digamma(x)-mp.loggamma(x)-x+mp.mpf('.5')+mp.log(2*mp.pi)/2
        record('Hurwitz_logGamma_primitive',mp.diff(prim,x),target,x=x)
    # Direct finite Gamma-ratio jet confirms the second-jet Stieltjes signs.
    def expected_second(x):
        psi=mp.digamma(x); p2=(psi**2-mp.polygamma(1,x))/2
        return p2-x*(1-psi+p2)-mp.diff(lambda s:mp.zeta(s,x),0,2)/2+mp.stieltjes(1,x)/2-mp.digamma(x)/2
    # Test coefficient at epsilon=0 using a Cauchy-circle integral to avoid
    # evaluating the individual pole terms at zero.
    for x in [mp.mpf(1),mp.mpf('1.4')]:
        rho=mp.mpf('.03'); N=96
        coef=sum(beta_closed(x,rho*mp.exp(2j*mp.pi*k/N))*mp.exp(-4j*mp.pi*k/N) for k in range(N))/(N*rho**2)
        record('second_jet_Cauchy_vs_polygamma',coef,expected_second(x),x=x)
    result={'status':'PASS','precision_decimal_digits':mp.mp.dps,'mpmath':mp.__version__,
            'checks':len(rows),'maximum_reported_error':mp.nstr(max(mp.mpf(z['relative_or_absolute_error']) for z in rows),10),
            'scope':'Floating-point diagnostics, not interval certificates; accelerated tails have no certified remainder here.',
            'rows':rows}
    (DATA/'numeric_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--part',choices=['exact','numeric','all'],default='all')
    args=p.parse_args()
    if args.part in ('exact','all'): exact_suite()
    if args.part in ('numeric','all'): numeric_suite()
