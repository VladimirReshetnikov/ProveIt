#!/usr/bin/env python3
"""Supplemental tests: general jet compiler, finite-head branches,
ordinary primitives, Stieltjes root filters, and higher spectral-ray jets.
All numerical tests are non-interval diagnostics.
"""
from __future__ import annotations
import argparse
import itertools
import json
import math
import platform
import time
from pathlib import Path
from typing import Any
import mpmath as mp
import sympy as sp
from verify import ROOT, cutoff_independent, h_numeric, loglambda


def exact_compiler() -> dict[str, Any]:
    L=sp.Symbol('L')
    K=8
    cases=[((1,2),(1,1),(-sp.Rational(1,5),sp.Rational(1,7))),
           ((0,0),(2,1),(-sp.Rational(1,4),sp.Rational(1,4))),
           ((1,0,2),(0,1,2),(-sp.Rational(1,7),sp.Rational(1,9),sp.Rational(1,6))),
           ((-1,2),(1,2),(-sp.Rational(1,5),sp.Rational(1,8))),
           ((0,1,0),(1,0,1),(-sp.Rational(1,6),sp.Rational(1,8),sp.Rational(1,5)))]
    def mul(a:list[Any], b:list[Any])->list[Any]:
        return [sp.expand(sum(a[j]*b[k-j] for j in range(k+1))) for k in range(K+1)]
    count=0
    for rs,ms,ds in cases:
        lhs=[sp.Integer(1)]+[sp.Integer(0)]*K
        # Independent multiplication of truncated binomial/log series.
        for r,m,d in zip(rs,ms,ds):
            fac=[(-1)**k*sp.rf(r,k)*d**k/sp.factorial(k) for k in range(K+1)]
            logfac=[L]+[(-1)**(k+1)*d**k/k for k in range(1,K+1)]
            for _ in range(m):fac=mul(fac,logfac)
            lhs=mul(lhs,fac)
        us=sp.symbols(f'u0:{len(rs)}');M=sum(ms)
        hs=[sp.Integer(1)]+[sp.Integer(0)]*K
        for u,d in zip(us,ds):
            hs=mul(hs,[sp.rf(u,k)*d**k/sp.factorial(k) for k in range(K+1)])
        for k in range(K+1):
            rhs=0
            for qs in itertools.product(*(range(m+1) for m in ms)):
                v=hs[k]
                for u,q in zip(us,qs):
                    if q:v=sp.diff(v,u,q)
                v=v.subs(dict(zip(us,rs)))
                rhs+=(-1)**(k+sum(qs))*math.prod(math.comb(m,q) for m,q in zip(ms,qs))*v*L**(M-sum(qs))
            if sp.expand(lhs[k]-rhs)!=0:raise AssertionError(('general jet compiler',rs,ms,k))
            count+=1
    return {'kind':'supplemental finite exact assertions','count':count,'passed':True}


def polylog_one_jet(z:Any, order:int, terms:int=360)->Any:
    """Euler-transformed defining series at s=1, differentiated termwise.
    For the tested q=2,3,4 roots, |z/(1-z)| <= 1/sqrt(2).
    Extra precision protects finite differences against binomial cancellation.
    """
    with mp.workdps(mp.mp.dps+150):
        values=[(-mp.log(n))**order/n for n in range(1,terms+1)]
        ratio=z/(1-z);power=ratio;total=mp.mpc(0)
        for _ in range(terms):
            total+=power*values[0]
            values=[values[j+1]-values[j] for j in range(len(values)-1)]
            power*=ratio
        return +total


def numeric(dps:int)->dict[str,Any]:
    mp.mp.dps=dps;rows=[];jet_cache={}
    def compare(name:str,lhs:Any,rhs:Any,tol:str='1e-34')->None:
        err=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))
        if err>=mp.mpf(tol):raise AssertionError((name,mp.nstr(err,12)))
        rows.append({'name':name,'relative_or_absolute_residual':mp.nstr(err,10)})
    # Arbitrary twists that cross frequency intervals. The finite head is
    # checked separately from the common-phase tail expansion.
    ts=[mp.mpf('-1.3'),mp.mpf('.2'),mp.mpf('2.4')]
    aa=[mp.mpc('.7','.1'),mp.mpf('-0.2'),mp.mpf('1.1')]
    c=mp.mpf('.5');N=6;hs=h_numeric(aa,[t-c for t in ts],200)
    for n in (-9,-6,-2,-1,0,1,3,5,6,9):
        actual=mp.exp(-sum(a*loglambda(n,t) for a,t in zip(aa,ts)))
        if abs(n)<N:
            # Use explicit amplitude and sign phase; no common-phase shortcut.
            repaired=mp.exp(-sum(a*mp.log(2*mp.pi*abs(n+t)) for a,t in zip(aa,ts)))
            repaired*=mp.exp(-mp.j*mp.pi/2*sum(a*mp.sign(n+t) for a,t in zip(aa,ts)))
        else:
            repaired=mp.exp(-sum(aa)*loglambda(n,c))*sum((-1)**k*h/(n+c)**k for k,h in enumerate(hs))
        compare(f'finite Fourier head repair n={n}',actual,repaired)
    # Ordinary p-fold primitives: numerical beta integral versus appended
    # shifted denominators, rather than the same factorial coefficient code.
    z=mp.mpc('.21','.07');a,b=mp.mpf('.8'),mp.mpf('1.2')
    alpha,beta=mp.mpf('1.1'),mp.mpf('.7')
    def multilerch(w:Any)->Any:
        return sum(w**n/((n+a)**alpha*(n+b)**beta) for n in range(100))
    for p in (1,2,3):
        lhs=z**p/mp.factorial(p-1)*mp.quad(lambda u:(1-u)**(p-1)*multilerch(z*u),[0,1])
        rhs=z**p*sum(z**n/((n+a)**alpha*(n+b)**beta*mp.fprod(n+j for j in range(1,p+1))) for n in range(100))
        compare(f'ordinary primitive order {p}',lhs,rhs)
    # Pole-aware cyclotomic Stieltjes formula: direct Stieltjes values versus
    # polylogarithm order derivatives at nontrivial roots of unity.
    for q,r in ((2,1),(3,1),(4,3)):
        omega=mp.exp(2j*mp.pi/q);ell=mp.log(q)
        for m in (0,1,2):
            rhs=ell**(m+1)/(m+1)
            for j in range(m+1):
                key=(q,r,j)
                if key not in jet_cache:
                    jet_cache[key]=sum(omega**(-r*h)*polylog_one_jet(omega**h,j) for h in range(1,q))
                atoms=jet_cache[key]
                rhs+=mp.binomial(m,j)*ell**(m-j)*((-1)**j*mp.stieltjes(j)+atoms)
            rhs*=(-1)**m
            compare(f'cyclotomic Stieltjes q={q}, r={r}, index={m}',mp.stieltjes(m,mp.mpf(r)/q),rhs)
    # Printed scalar example, checked against the independent EM evaluator.
    a,b=mp.mpf('.5'),mp.mpf('.75')
    rhs=mp.stieltjes(1)-2*mp.euler*mp.log(2)-mp.log(2)**2
    rhs+=sum((-1)**(k+1)*(mp.mpf(2)**(k+1)-1)*mp.zeta(k+1)/(mp.mpf(4)**k*k) for k in range(1,160))
    compare('printed quarter-shift constant',cutoff_independent(0,1,a,b),rhs)
    # Higher ray derivatives by Cauchy extraction from the full regularized
    # meromorphic function versus the explicit coefficient formula.
    cs=sp.Integer(1);ts_exact=[sp.Rational(49,50),sp.Rational(51,50)];ws_exact=[sp.Integer(1),sp.Integer(2)]
    u=sp.Symbol('u');ds_exact=[t-cs for t in ts_exact]
    K=32;hpoly=[sp.Integer(1)]
    for k in range(1,K+1):
        hpoly.append(sp.expand(sum(u*sum(w*d**j for w,d in zip(ws_exact,ds_exact))*hpoly[k-j] for j in range(1,k+1))/k))
    hc=[[mp.mpf(str(sp.N(sp.Poly(p,u).nth(q),dps))) for q in range(4)] for p in hpoly]
    ws=list(map(mp.mpf,ws_exact));ds=[mp.mpf(str(t)) for t in ['-.02','.02']]
    W=sum(ws);D=sum(w*d for w,d in zip(ws,ds));c=mp.mpf(1)
    Q=48;rho=mp.mpf('.04');values=[]
    for j in range(Q):
        t=rho*mp.exp(2j*mp.pi*j/Q);A=W*t
        hs=h_numeric([t*w for w in ws],ds,K)
        value=mp.zeta(A,c)-D/W-t*D*(mp.zeta(1+A,c)-1/A)
        value+=sum((-1)**k*hs[k]*mp.zeta(A+k,c) for k in range(2,K+1))
        values.append(value)
    for m in (1,2,3):
        lhs=mp.factorial(m)*sum(values[j]*mp.exp(-2j*mp.pi*j*m/Q) for j in range(Q))/(Q*rho**m)
        rhs=W**m*mp.zeta(0,c,derivative=m)+(-1)**m*m*D*W**(m-1)*mp.stieltjes(m-1,c)
        rhs+=sum((-1)**k*sum(mp.binomial(m,q)*mp.factorial(q)*hc[k][q]*W**(m-q)*mp.zeta(k,c,derivative=m-q) for q in range(1,min(m,k)+1)) for k in range(2,K+1))
        compare(f'spectral-ray Cauchy derivative {m}',lhs,rhs)
    return {'kind':'supplemental floating-point diagnostics','dps':dps,'count':len(rows),'checks':rows,'passed':True}


def main()->None:
    parser=argparse.ArgumentParser();parser.add_argument('--dps',type=int,default=65)
    args=parser.parse_args()
    if args.dps<55:parser.error('At least 55 digits are needed.')
    start=time.perf_counter();result={'exact':exact_compiler(),'numerical':numeric(args.dps)}
    result['runtime_seconds']=round(time.perf_counter()-start,3)
    result['environment']={'python':platform.python_version(),'sympy':sp.__version__,'mpmath':mp.__version__}
    (ROOT/'validation').mkdir(exist_ok=True)
    path=ROOT/'validation'/'extended.json';path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'passed':True,'exact':result['exact']['count'],'numerical':result['numerical']['count'],'runtime':result['runtime_seconds']}))

if __name__=='__main__':main()
