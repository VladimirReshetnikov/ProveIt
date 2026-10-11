#!/usr/bin/env python3
"""Reproducible checks for Unequal-Twist Stieltjes Jets.

Exact assertions are finite algebraic checks, not formal analytic proofs.
Numerical residuals are diagnostics, not interval certificates.
Python 3.10+, sympy, mpmath. Run from any working directory.
"""
from __future__ import annotations
import argparse
import json
import math
import platform
import time
from functools import lru_cache
from pathlib import Path
from typing import Any

import mpmath as mp
import sympy as sp
from sympy.functions.combinatorial.numbers import stirling

ROOT = Path(__file__).resolve().parents[1]


def exact_checks() -> dict[str, Any]:
    counts: dict[str, int] = {}
    def check(name: str, truth: Any) -> None:
        if not bool(truth):
            raise AssertionError(name)
        counts[name] = counts.get(name, 0) + 1
    u, x, v = sp.symbols('u x v')
    for r in range(5):
        for k in range(13):
            poly = sp.Poly(sp.rf(r + u, k).expand() / sp.factorial(k), u)
            for m in range(6):
                actual = sp.factorial(m) * poly.nth(m)
                if r == 0:
                    expected = (sp.factorial(m) * stirling(k, m, kind=1)
                                / sp.factorial(k)) if m <= k else 0
                else:
                    # Independent elementary-symmetric construction of the Bell coefficient.
                    p = sp.prod(1 + u / sp.Integer(r + j) for j in range(k))
                    expected = sp.rf(r, k) / sp.factorial(k) * sp.factorial(m) * sp.expand(p).coeff(u, m)
                check('Pochhammer derivatives including zero', sp.simplify(actual - expected) == 0)
    # Multicentre coefficient recurrence against direct finite products.
    for alphas, ds in [((sp.Rational(2,3), sp.Rational(-1,4)), (sp.Rational(-1,7),sp.Rational(2,9))),
                       ((2,0,3), (sp.Rational(-1,5),sp.Rational(1,6),sp.Rational(1,4))),
                       ((u,v), (sp.Rational(-1,3),sp.Rational(1,3)))]:
        upto = 9 if u not in alphas else 6
        h = [sp.Integer(1)]
        for k in range(1, upto+1):
            h.append(sp.expand(sum(sum(a*d**ell for a,d in zip(alphas,ds)) * h[k-ell]
                                  for ell in range(1,k+1))/k))
        prod = [sp.Integer(1)] + [sp.Integer(0)] * upto
        for a,d in zip(alphas,ds):
            fac = [sp.rf(a,k)*d**k/sp.factorial(k) for k in range(upto+1)]
            prod = [sp.expand(sum(prod[j]*fac[k-j] for j in range(k+1))) for k in range(upto+1)]
        for k in range(upto+1):
            check('Multicentre recurrence', sp.expand(h[k]-prod[k]) == 0)
    # Formal log product and the ordinary-Gamma convolution coefficients.
    L = sp.Symbol('L')
    maxk = 24
    minus = [L]+[-sp.Rational(1,j) for j in range(1,2*maxk+1)]
    plus = [L]+[sp.Rational((-1)**(j+1),j) for j in range(1,2*maxk+1)]
    coeff = [sp.expand(sum(minus[j]*plus[k-j] for j in range(k+1))) for k in range(2*maxk+1)]
    for k in range(1,maxk+1):
        eta = sp.harmonic(2*k-1)-sp.harmonic(k-1)
        check('Symmetric mixed-log coefficients', sp.expand(coeff[2*k]+(L+eta)/k) == 0)
        check('Odd symmetric coefficients vanish', coeff[2*k-1] == 0)
    for k in range(maxk+1):
        S = sum((sp.harmonic(2*j-1)-sp.harmonic(j-1))/j for j in range(1,k+1))
        lhs = sum(coeff[2*j] for j in range(k+1))
        rhs = L**2-sp.harmonic(k)*L-S
        check('Gamma-convolution harmonic coefficients', sp.expand(lhs-rhs) == 0)
    # The coefficient formula in the all-order cutoff constants.
    for k in range(1,16):
        p = sp.Poly(sp.rf(u,k).expand()/sp.factorial(k),u)
        for n in range(1,6):
            for q in range(1,n+1):
                a = sp.binomial(n,q)*sp.factorial(q)*p.nth(q)
                b = sp.binomial(n,q)*sp.factorial(q)*stirling(k,q,kind=1)/sp.factorial(k) if q<=k else 0
                check('Cutoff-jet Stirling coefficients', a == b)
    # Mixed monodromy: exact nonzero iterated differences.
    La,Lb,h = sp.symbols('La Lb h')
    for m in range(1,6):
        for n in range(1,6):
            f = La**m*Lb**n
            d = f
            for _ in range(m):
                d=sp.expand(d.subs(La,La+h)-d)
            for _ in range(n):
                d=sp.expand(d.subs(Lb,Lb+h)-d)
            check('Mixed monodromy certificates', sp.expand(d-sp.factorial(m)*sp.factorial(n)*h**(m+n)) == 0)
    for q in range(10):
        for f in (La**q,Lb**q):
            delta_a=sp.expand(f.subs(La,La+h)-f)
            delta_b=sp.expand(delta_a.subs(Lb,Lb+h)-delta_a)
            check('Single-centre mixed monodromy vanishes', delta_b == 0)
    # Rational integer-order baseline, checked independently by clearing denominators.
    D=sp.Symbol('D',nonzero=True)
    for r in range(1,5):
        for s in range(1,5):
            rhs=sum((-1)**(r-j)*sp.binomial(r+s-j-1,r-j)*x**(-j)/D**(r+s-j) for j in range(1,r+1))
            rhs+=sum((-1)**r*sp.binomial(r+s-j-1,s-j)*(x+D)**(-j)/D**(r+s-j) for j in range(1,s+1))
            check('Integer partial fractions', sp.cancel(rhs-1/(x**r*(x+D)**s)) == 0)
    # Reject three deliberately damaged formulas.
    check('Corruption controls rejected', sp.expand(coeff[2]+(L-1)) != 0)
    check('Corruption controls rejected', sp.expand((L+sp.EulerGamma)**2-(L**2+2*sp.EulerGamma*L+sp.EulerGamma**2+sp.zeta(2))) != 0)
    check('Corruption controls rejected', sp.cancel((1/x+1/(x+D))/D-1/(x*(x+D))) != 0)
    return {'kind':'finite exact assertions','total':sum(counts.values()),'families':counts,'passed':True}


def mpc_json(z: Any) -> str:
    return mp.nstr(z, 16)


def h_numeric(alphas: list[Any], ds: list[Any], upto: int) -> list[Any]:
    h=[mp.mpc(1)]
    powers=[None]+[sum(a*d**ell for a,d in zip(alphas,ds)) for ell in range(1,upto+1)]
    for k in range(1,upto+1):
        h.append(sum(powers[ell]*h[k-ell] for ell in range(1,k+1))/k)
    return h


def loglambda(n: int, theta: Any) -> Any:
    return mp.log(2*mp.pi*abs(n+theta))+mp.j*mp.pi/2*mp.sign(n+theta)


def spectral_checks(dps: int) -> dict[str,Any]:
    mp.mp.dps=dps
    rows=[]
    def compare(name: str, lhs: Any, rhs: Any, tolerance: str='1e-38') -> None:
        residual=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))
        if residual>=mp.mpf(tolerance):
            raise AssertionError((name,mp.nstr(residual,10),mp.nstr(lhs,10),mp.nstr(rhs,10)))
        rows.append({'name':name,'relative_or_absolute_residual':mp.nstr(residual,8)})
    parameters=[([mp.mpc('0.7','0.2'),mp.mpc('-0.3','0.1')],[mp.mpf('.3'),mp.mpf('.6')]),
                ([mp.mpf('1.2'),mp.mpf('.8'),mp.mpf('-.6')],[mp.mpf('.25'),mp.mpf('.5'),mp.mpf('.65')]),
                ([mp.mpf('0'),mp.mpf('2')],[mp.mpf('.35'),mp.mpf('.65')])]
    for idx,(alphas,ts) in enumerate(parameters):
        c=(min(ts)+max(ts))/2; ds=[t-c for t in ts]; A=sum(alphas)
        hs=h_numeric(alphas,ds,180)
        for n in (-7,-2,-1,0,1,5):
            L=loglambda(n,c)
            lhs=mp.exp(-sum(a*loglambda(n,t) for a,t in zip(alphas,ts)))
            rhs=mp.exp(-A*L)*sum((-1)**k*h/(n+c)**k for k,h in enumerate(hs))
            compare(f'multicentre {idx}, mode {n}',lhs,rhs)
    # Explicit symmetric pure and integrated mixed first jets.
    for c,d in [(mp.mpf('.5'),mp.mpf('.2')),(mp.mpf('.4'),mp.mpf('.1'))]:
        for n in (-4,-1,0,3):
            La,Lb,Lc=loglambda(n,c-d),loglambda(n,c+d),loglambda(n,c)
            u=d/(n+c)
            rhs=Lc**2-sum(u**(2*k)/k*(Lc+mp.harmonic(2*k-1)-mp.harmonic(k-1)) for k in range(1,100))
            compare(f'symmetric log {c}, mode {n}',La*Lb,rhs)
            S=mp.mpf(0); terms=[]
            for k in range(100):
                if k: S+=(mp.harmonic(2*k-1)-mp.harmonic(k-1))/k
                terms.append(u**(2*k)*(Lc**2-mp.harmonic(k)*Lc-S))
            rhs=mp.exp(-2*Lc)*sum(terms)
            compare(f'integrated symmetric {c}, mode {n}',La*Lb*mp.exp(-La-Lb),rhs)
    # The normalizing contact term, including the zero coefficient.
    for n in (-3,-1,0,2):
        a,b=mp.mpf('.3'),mp.mpf('.7');c=(a+b)/2;d=(b-a)/2
        La,Lb,Lc=loglambda(n,a),loglambda(n,b),loglambda(n,c)
        U0a,U0b,U0c=-(La+mp.euler),-(Lb+mp.euler),-(Lc+mp.euler)
        U1c=((Lc+mp.euler)**2+mp.zeta(2))/2
        tail=sum((d/(n+c))**(2*k)/k*(Lc+mp.harmonic(2*k-1)-mp.harmonic(k-1)) for k in range(1,100))
        rhs=2*U1c+2*mp.euler*U0c-mp.euler*(U0a+U0b)-mp.zeta(2)-tail
        compare(f'contact normalization mode {n}',U0a*U0b,rhs)
    return {'kind':'floating-point diagnostics','dps':dps,'count':len(rows),'checks':rows,'passed':True}


@lru_cache(maxsize=None)
def zd(s: int, a_text: str, order: int) -> Any:
    return mp.zeta(s,mp.mpf(a_text),derivative=order)


def cutoff_series(m: int,n: int,a: Any,b: Any,upto: int=105) -> Any:
    M=m+n;d=b-a
    total=mp.stieltjes(M,a)
    for k in range(1,upto+1):
        term=mp.mpf(0)
        for q in range(1,min(n,k)+1):
            D=mp.mpf(int(stirling(k,q,kind=1)))*mp.factorial(q)/mp.factorial(k)
            term+=mp.binomial(n,q)*D*zd(k+1,mp.nstr(a,mp.mp.dps),M-q)
        total+=(-1)**M*(-d)**k*term
    return total


def cutoff_independent(m:int,n:int,a:Any,b:Any,N:int=55,K:int=20) -> Any:
    """Independent convergent difference sum with an Euler--Maclaurin tail.
    The tail integral is transformed to a bounded interval. No zeta expansion
    of the mixed summand is used. The remainder is tested, not certified.
    """
    M=m+n;d=b-a
    if n==0 or d==0:return mp.stieltjes(M,a)
    def g(x:Any)->Any:
        L=mp.log(x+a);v=mp.log1p(d/(x+a))
        return sum(mp.binomial(n,q)*L**(M-q)*v**q for q in range(1,n+1))/(x+a)
    def integrand(t:Any)->Any:
        if t==0:return mp.mpf(0)
        return sum(mp.binomial(n,q)*(-mp.log(t))**(M-q)*mp.log1p(d*t)**q for q in range(1,n+1))/t
    integral=mp.quad(integrand,[0,1/(N+a)])
    coeff=mp.taylor(g,mp.mpf(N),2*K-1)
    tail=integral+g(N)/2-sum(mp.bernoulli(2*k)*coeff[2*k-1]/(2*k) for k in range(1,K+1))
    return mp.stieltjes(M,a)+sum(g(j) for j in range(N))+tail


def scalar_checks(dps:int)->dict[str,Any]:
    mp.mp.dps=dps;zd.cache_clear();rows=[]
    def compare(name:str,lhs:Any,rhs:Any,tolerance:str='1e-35')->None:
        residual=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))
        if residual>=mp.mpf(tolerance):raise AssertionError((name,mp.nstr(residual,10)))
        rows.append({'name':name,'relative_or_absolute_residual':mp.nstr(residual,8),
                     'value':mp.nstr(lhs,30)})
    for a,b in [(mp.mpf('1.25'),mp.mpf('1.5')),(mp.mpf('.8'),mp.mpf('.64'))]:
        for m,n in [(0,1),(1,1),(0,2),(2,1),(1,2),(0,3)]:
            compare(f'cutoff ({m},{n}), a={a}, b={b}',cutoff_series(m,n,a,b),cutoff_independent(m,n,a,b))
    a,b=mp.mpf('1.25'),mp.mpf('1.5')
    c01=cutoff_series(0,1,a,b)
    via_int=mp.stieltjes(1,a)+mp.quad(lambda t:(mp.digamma(t)-mp.digamma(a))/(t-a) if t!=a else mp.polygamma(1,a),[a,b])
    compare('digamma divided-difference integral',c01,via_int)
    # Differential recursion checked against its independently convergent series.
    for m,n in [(0,1),(1,1),(0,2),(1,2)]:
        # d/db: compute difference-sum derivative with Euler--Maclaurin.
        f=lambda x:n*mp.log(x+a)**m*mp.log(x+b)**(n-1)/((x+a)*(x+b))
        N,K=55,20
        integ=mp.quad(lambda t:n*(-mp.log(t))**m*(mp.log1p((b-a)*t)-mp.log(t))**(n-1)/(1+(b-a)*t) if t else 0,[0,1/(N+a)])
        co=mp.taylor(f,mp.mpf(N),2*K-1)
        lhs=sum(f(j) for j in range(N))+integ+f(N)/2-sum(mp.bernoulli(2*k)*co[2*k-1]/(2*k) for k in range(1,K+1))
        rhs=n/(b-a)*(cutoff_series(m,n-1,a,b)-cutoff_series(n-1,m,b,a))
        compare(f'cutoff differential recursion {m},{n}',lhs,rhs)
    # A Gamma primitive identity using Fubini on the divided-difference integral.
    d=b-a
    lhs=mp.stieltjes(1,a)*d+mp.quad(lambda t:(b-t)*(mp.digamma(t)-mp.digamma(a))/(t-a) if t!=a else (b-a)*mp.polygamma(1,a),[a,b])
    rhs=d*c01-mp.loggamma(b)+mp.loggamma(a)+d*mp.digamma(a)
    compare('ordinary Gamma primitive',lhs,rhs)
    # Rational polylogarithm filter in the open disk, including an order derivative.
    z=mp.mpc('.31','.12')
    for q,r in [(3,1),(4,3),(5,2)]:
        w=mp.exp(mp.log(z)/q);omega=mp.exp(2j*mp.pi/q);s=mp.mpf('1.3')
        for order in (0,1):
            lhs=sum(z**n*(-mp.log(n+mp.mpf(r)/q))**order/(n+mp.mpf(r)/q)**s for n in range(180))
            def filt(t:Any)->Any:
                return q**(t-1)*w**(-r)*sum(omega**(-r*h)*mp.polylog(t,omega**h*w) for h in range(q))
            rhs=filt(s) if not order else mp.diff(filt,s)
            compare(f'rational polylog filter {q},{r}, derivative {order}',lhs,rhs)
    # Spectral-ray value and first derivative: independent direct derivatives
    # of the normally convergent series, versus the finite Gamma expression.
    for ts,ws in [([mp.mpf('1.1'),mp.mpf('1.4')],[mp.mpf('1'),mp.mpf('2')]),
                  ([mp.mpf('.8'),mp.mpf('1.0'),mp.mpf('1.2')],[mp.mpf('2'),mp.mpf('-1'),mp.mpf('3')])]:
        c=(min(ts)+max(ts))/2;ds=[t-c for t in ts];W=sum(ws);D=sum(w*d for w,d in zip(ws,ds))
        ray0=mp.zeta(0,c)-D/W
        compare('spectral ray zero value',ray0,mp.mpf('.5')-sum(w*t for w,t in zip(ws,ts))/W)
        ray1=W*mp.zeta(0,c,derivative=1)-D*mp.stieltjes(0,c)
        ray1+=sum((-1)**k*sum(w*d**k for w,d in zip(ws,ds))/k*mp.zeta(k,c) for k in range(2,100))
        compare('spectral ray Gamma derivative',ray1,sum(w*(mp.loggamma(t)-mp.log(2*mp.pi)/2) for w,t in zip(ws,ts)))
    return {'kind':'floating-point diagnostics','dps':dps,'count':len(rows),'checks':rows,'passed':True}


def gamma_p(x:Any,p:int,q:int)->Any:
    theta=mp.mpf(p)/q;z=mp.exp(-2j*mp.pi*theta)
    bracket=sum(z**r*mp.loggamma((x+r)/q) for r in range(q))-(mp.euler+mp.log(q))/(1-z)
    return mp.exp(-2j*mp.pi*theta*x)*bracket


def gamma_checks(dps:int)->dict[str,Any]:
    mp.mp.dps=dps;rows=[];ell=mp.log(2*mp.pi)
    for p,q in [(1,4),(1,3)]:
        d=mp.mpf('.5')-mp.mpf(p)/q
        for x in [mp.mpf('0'),mp.mpf('.5')]:
            def f(t:Any)->Any:
                y=x-t if t<x else x-t+1
                return gamma_p(t,p,q)*gamma_p(y,q-p,q)
            lhs=mp.quad(f,[0,1] if x==0 else [0,x,1])
            rhs=0;S=mp.mpf(0)
            for k in range(80):
                if k:S+=(mp.harmonic(2*k-1)-mp.harmonic(k-1))/k
                r=2*k+2
                if x==0:
                    Z=[mp.zeta(r,mp.mpf('.5'),derivative=j) for j in range(3)]
                    term=-(Z[2]+(mp.harmonic(k)-2*ell)*Z[1]+(ell**2-mp.harmonic(k)*ell-S-mp.pi**2/4)*Z[0])/(2*mp.pi**2)
                else:
                    Q0=mp.zeta(r,mp.mpf('.25'))-mp.zeta(r,mp.mpf('.75'))
                    Q1=mp.zeta(r,mp.mpf('.25'),derivative=1)-mp.zeta(r,mp.mpf('.75'),derivative=1)
                    A=mp.mpf(2)**(-r)*Q0
                    A1=mp.mpf(2)**(-r)*(Q1-mp.log(2)*Q0)
                    term=1j/(4*mp.pi)*(2*A1+(mp.harmonic(k)-2*ell)*A)
                rhs+=d**(2*k)*term
            err=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))
            if err>mp.mpf('1e-35'):raise AssertionError(('Gamma convolution',p,q,x,mp.nstr(err,10)))
            rows.append({'name':f'ordinary Gamma convolution {p}/{q}, x={x}', 'relative_or_absolute_residual':mp.nstr(err,8),'value':mp.nstr(lhs,30)})
    return {'kind':'independent ordinary-integral diagnostics','dps':dps,'count':len(rows),'checks':rows,'passed':True}


def main()->None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--part',choices=['exact','spectral','scalar','gamma','all'],default='all')
    parser.add_argument('--dps',type=int,default=65)
    args=parser.parse_args()
    if args.dps<55:parser.error('At least 55 digits are needed for the default tolerances.')
    functions={'exact':lambda:exact_checks(),'spectral':lambda:spectral_checks(args.dps),'scalar':lambda:scalar_checks(args.dps),'gamma':lambda:gamma_checks(args.dps)}
    ROOT.joinpath('validation').mkdir(exist_ok=True)
    for name,fun in functions.items():
        if args.part not in ('all',name):continue
        t=time.perf_counter();result=fun();result['runtime_seconds']=round(time.perf_counter()-t,3)
        result['environment']={'python':platform.python_version(),'sympy':sp.__version__,'mpmath':mp.__version__}
        path=ROOT/'validation'/f'{name}.json';path.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({'part':name,'passed':True,'count':result.get('count',result.get('total')),'runtime':result['runtime_seconds'],'report':str(path)}),flush=True)

if __name__=='__main__':main()
