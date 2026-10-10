#!/usr/bin/env python3
"""Independent high-precision diagnostics; not rigorous error enclosures."""
from __future__ import annotations
import json, platform, time
from pathlib import Path
from functools import lru_cache
import mpmath as mp
from gauss_hurwitz import (as_mp,coefficient_jets,convergent_jet,closed_jet,
                           resonant_value,term_jet,e_jet,exp_jet,mul,tail_harmonic_sum)
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=65
ROWS=[]

def record(name, lhs, rhs, threshold=mp.mpf('1e-30'), detail=None):
    err=abs(lhs-rhs)/max(1,abs(rhs))
    if err >= threshold:
        raise AssertionError(f'{name}: scaled error {mp.nstr(err,12)} >= {threshold}')
    row={'name':name,'lhs':mp.nstr(lhs,54),'rhs':mp.nstr(rhs,54),
         'scaled_error':mp.nstr(err,12),'tolerance':str(threshold),'status':'PASS'}
    if detail is not None:
        row['configuration']=detail
    ROWS.append(row)
    print(name,mp.nstr(err,5),flush=True)

@lru_cache(maxsize=256)
def left(a,b,c,N,m,large=False):
    return convergent_jet(a,b,c,N,m,M=108 if large else 72,J=26 if large else 22)


def f_regularized(a,b,u,z,L=6):
    """Stable regularized 2F1 via an exact finite head and regular 3F2 tail."""
    a,b=as_mp(a),as_mp(b)
    head=mp.fsum(mp.gamma(n+a)*mp.gamma(n+b)/mp.factorial(n)
                *mp.rgamma(n+a+b+u)*z**n for n in range(L))
    pref=mp.gamma(L+a)*mp.gamma(L+b)/mp.factorial(L)*mp.rgamma(L+a+b+u)*z**L
    return head+pref*mp.hyper([1,L+a,L+b],[L+1,L+a+b+u],z)


def main():
    start=time.time()
    cases=[]
    for N in range(4):
        for m in range(4):
            cases.append(('1/2','1/2',1,N,m))
    cases += [('1/3','2/3','2/3',N,m) for N,m in [(0,0),(0,2),(1,1),(2,2),(3,0)]]
    cases += [('2/3','5/4','7/4',N,m) for N,m in [(0,1),(1,0),(2,1),(3,2)]]
    cases += [(1,'1/2',1,2,m) for m in [0,1,2]]
    cases += [(2,3,'4/3',3,m) for m in [0,1,2]]
    for a,b,c,N,m in cases:
        small=left(a,b,c,N,m)
        large=left(a,b,c,N,m,True)
        rhs=closed_jet(a,b,c,N,m)
        record(f'spectral jet ({a},{b};c={c}) N={N},m={m}',large,rhs,
               detail={'M':108,'J':26,'repeat_M':72,'repeat_J':22,
                       'repeat_scaled_difference':mp.nstr(abs(small-large)/max(1,abs(large)),12)})
        if abs(small-large)/max(1,abs(large)) >= mp.mpf('1e-28'):
            raise AssertionError('asymptotic-tail repeat failed')
        if m==0:
            record(f'closed resonant value ({a},{b};{c}) N={N}',rhs,resonant_value(a,b,c,N),mp.mpf('1e-55'))
    L=mp.log(2); A=mp.euler+4*L
    explicit_N1=-(A-3)**2/8+5*mp.zeta(2)/8+mp.mpf(11)/8-3*mp.euler/2-mp.stieltjes(1)/4+mp.log(2*mp.pi)/2
    record('printed first negative-resonance jet',left('1/2','1/2',1,1,1,True),explicit_N1)
    record('zero-term revival n=0,N=1',term_jet(0,'1/2','1/2',1,1)[1],mp.pi,mp.mpf('1e-55'))
    # Gamma-normalized differences produce complete finite harmonic sums.
    gj=exp_jet([0,-mp.euler,mp.zeta(2)/2,-mp.zeta(3)/3,mp.zeta(4)/4],4)
    diffs=[left('1/2','1/2',1,0,m,True)-left(1,1,1,0,m,True) for m in range(4)]
    normalized=mul(gj,diffs,3)
    lambdalog=[0,4*L]+[2*((-1)**k)*(2-2**k)*mp.zeta(k)/k for k in range(2,5)]
    bjet=exp_jet(lambdalog,4)
    for m in range(4):
        record(f'complete finite harmonic family m={m}',normalized[m],bjet[m+1])
    # Harmonic Stieltjes formula, combining independent spectral series.
    spectral0=left('1/2','1/2',1,0,0,True)
    spectral1=left('1/2','1/2',1,0,1,True)
    harmonic_stieltjes=mp.euler*spectral0-spectral1
    target=5*mp.zeta(2)/2-8*L**2-mp.euler**2/2-mp.stieltjes(1)
    record('printed H_n Stieltjes identity',harmonic_stieltjes,target)
    for x in ['1/2','2/3',1]:
        for k in [1,2,3]:
            got=tail_harmonic_sum(x,k,108,26)
            record(f'harmonic-tail collapse x={x},k={k}',got,2*mp.zeta(2*k+1,as_mp(x)))
    # Interior z checks of polylogarithmic subtraction, with stable regularization.
    z=mp.mpf('0.37')
    for N,m in [(0,0),(0,1),(1,0),(1,1),(2,2)]:
        K=N+1
        aa=[[as_mp(v) for v in row] for row in coefficient_jets('1/2','1/2',1,-N,K,m)]
        series=mp.mpf(0)
        for n in range(160):
            x=n+1
            logs=[(-mp.log(x))**q/mp.factorial(q) for q in range(m+1)]
            sub=sum(mp.mpf(x)**(N-1-j)*sum(aa[j][q]*logs[m-q] for q in range(m+1)) for j in range(K))
            series+=(term_jet(n,'1/2','1/2',N,m)[m]-sub)*z**(n+1)
        fjet=mp.diff(lambda t:z*f_regularized('1/2','1/2',-N+t,z),0,m)/mp.factorial(m)
        counter=sum(aa[j][q]*mp.diff(lambda s:mp.polylog(s,z),1-N+j,m-q)/mp.factorial(m-q)
                    for j in range(K) for q in range(m+1))
        record(f'polylog interior N={N},m={m}',series,fjet-counter,mp.mpf('1e-50'))
    # Derivative telescope away from poles, evaluated without infinite sums.
    for K in [1,2,3]:
        u=mp.mpf('0.37');a='2/3';b='5/4';cv=mp.mpf('1.2')
        # Use exact coefficient polynomials lambdified for stable differentiation.
        import sympy as sp
        cc=sp.symbols('c')
        pol=coefficient_jets(a,b,cc,sp.Rational(37,100),K,0)
        fs=[sp.lambdify(cc,row[0],'mpmath') for row in pol]
        fun=lambda c:-sum(fs[j](c)*mp.zeta(1+u+j,c) for j in range(K))
        rhs=(u+K)*fs[-1](cv)*mp.zeta(1+u+K,cv)
        record(f'primitive telescope K={K}',mp.diff(fun,cv),rhs,mp.mpf('1e-55'))
    result={'status':'PASS','diagnostic_count':len(ROWS),'working_decimal_digits':mp.mp.dps,
            'python':platform.python_version(),'mpmath':mp.__version__,
            'largest_scaled_error':mp.nstr(max(mp.mpf(r['scaled_error']) for r in ROWS),12),
            'elapsed_seconds':round(time.time()-start,3),
            'warning':'Asymptotic-tail numerical diagnostics, not rigorous interval certificates. Analytic proofs are in article.pdf.',
            'checks':ROWS}
    (ROOT/'results'/'numerical_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'PASS: {len(ROWS)} diagnostics; max error {result["largest_scaled_error"]}; {result["elapsed_seconds"]} s')

if __name__=='__main__':
    main()
