#!/usr/bin/env python3
"""Independent numerical diagnostics, NOT interval certificates.

Usage: python code/verify_numeric.py --part kernels|moments|spectral|residues
The four parts write separate JSON receipts. Use --part all to run all.
Dependencies: mpmath, numpy, scipy. No network calls.
"""
from __future__ import annotations
import argparse,json,time
from pathlib import Path
import mpmath as mp
import numpy as np
from scipy import special
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=40

def f(s,x): return -mp.polylog(s,-x)
def err(a,b): return abs(a-b)/max(1,abs(a),abs(b))

def E(v,a=1):
    if abs(v)<mp.mpf('1e-30'): return 1
    return v*mp.zeta(v+1,a)

def W(t,q):
    if t==0:return (q-1)*(q-2)/2
    d=q-2
    # Stable second divided difference: no subtraction of nearly equal O(1) terms.
    return mp.exp(-q*t)*(d*d*mp.hyp1f1(1,3,d*t)+d*mp.hyp1f1(1,3,-t))/2*(t/(-mp.expm1(-t)))**2

def bell_weight(n,t):
    L=mp.log(t)+mp.euler
    return [mp.mpf(1),L,L*L-mp.zeta(2),L**3-3*mp.zeta(2)*L+2*mp.zeta(3)][n]

def record(rows,name,a,b,tol):
    e=err(a,b)
    assert e<mp.mpf(tol),(name,mp.nstr(e,12),mp.nstr(a,20),mp.nstr(b,20))
    rows.append({'name':name,'relative_error':mp.nstr(e,12),'tolerance':str(tol),
                 'value':mp.nstr(a,28)})

def kernels():
    rows=[]
    for q in map(mp.mpf,['0.7','1.5','2.3','3']):
        for n in range(3):
            value=mp.quad(lambda t:W(t,q)*bell_weight(n,t),[0,1,5,mp.inf])
            rhs=(-1)**n*(mp.stieltjes(n,q)-mp.stieltjes(n))-(mp.diff(lambda z:mp.zeta(z,q)-mp.zeta(z),0,n) if n else mp.zeta(0,q)-mp.zeta(0))
            record(rows,f'W Stieltjes moment q={q} n={n}',value,rhs,'1e-30')
    for q in map(mp.mpf,['0.8','1.7','3.2']):
        primitive=lambda a:(a-1)**2/2-mp.loggamma(a)-mp.euler*(a-1)
        record(rows,f'anchored Gamma primitive q={q}',mp.diff(primitive,q),mp.quad(lambda t:W(t,q),[0,1,mp.inf]),'1e-30')
    return rows

def moments():
    rows=[]
    F2=lambda u:mp.polylog(2,u)+mp.log1p(-u)**2/2
    for r in range(7):
        lhs=mp.quad(lambda u:F2(u)*(-mp.log1p(-u))**r,[0,mp.mpf('.5'),mp.mpf('.9'),1])
        rhs=mp.factorial(r)*sum((j+1)*mp.zeta(j+2) for j in range(r+1))
        record(rows,f'all logarithmic dilogarithm moment r={r}',lhs,rhs,'1e-29')
    lhs=mp.quad(lambda u:F2(u)**2,[0,mp.mpf('.5'),mp.mpf('.9'),1])
    record(rows,'dilogarithm square',lhs,mp.mpf(17)/2*mp.zeta(4),'1e-30')
    lhs=mp.quad(lambda u:f(3,u/(1-u))*(-mp.log1p(-u)),[0,mp.mpf('.5'),mp.mpf('.9'),1])
    record(rows,'logarithm times trilogarithm',lhs,2*mp.zeta(3)+mp.mpf(17)/4*mp.zeta(4),'1e-29')
    return rows

def single_barnes(a,s,lam):
    c=(max(mp.mpf(0),1-mp.re(a))+min(mp.mpf(1),1-mp.re(lam)))/2
    def integrand(t):
        p=c+1j*t
        return mp.pi/mp.sin(mp.pi*p)*(p+a-1)**(-s)*mp.gamma(1+p)*mp.gamma(1-lam-p)/mp.gamma(2-lam)
    return mp.quad(integrand,[-mp.inf,-5,0,5,mp.inf])/(2*mp.pi)

def residues():
    rows=[]
    cases=[(mp.mpf(1),mp.mpf('4.2'),mp.mpf('.2')),
           (mp.mpf('2.3'),mp.mpc('4.5','.2'),mp.mpf('-.15')),
           (mp.mpf('.7'),mp.mpf(5),mp.mpf('.12'))]
    for a,s,lam in cases:
        def term(k):
            u=k+a-1
            lb=mp.loggamma(k+1)-mp.loggamma(k+lam)-s*mp.log(u)
            lr=mp.loggamma(k+1-lam)+mp.loggamma(k+lam)-mp.loggamma(k)-mp.loggamma(k+1)-s*mp.log1p(-lam/u)
            return mp.exp(lb)*mp.expm1(lr)
        rhs=mp.pi/(mp.sin(mp.pi*lam)*mp.gamma(2-lam))*mp.nsum(term,[1,mp.inf])
        lhs=single_barnes(a,s,lam)
        record(rows,f'coalescing residue generator a={a},s={s},lambda={lam}',lhs,rhs,'2e-12')
    for lam in (mp.mpf('.15'),mp.mpf('-.2')):
        record(rows,f'dilogarithm Gamma generator lambda={lam}',single_barnes(1,2,lam),mp.polygamma(1,1-lam)/(1-lam),'1e-29')
    return rows

def double_barnes(s,t,b,N,z,w,step=.045,T=13.):
    # Independent machine-precision two-dimensional trapezoid, not mpmath quadrature.
    c1,c2=.31,.37
    ys=np.arange(-int(T/step),int(T/step)+1)*step
    p=c1+1j*ys[:,None]; q=c2+1j*ys[None,:]
    logbeta=special.loggamma(b+p+q)+special.loggamma(N-b-p-q)-special.loggamma(N)
    integrand=(np.pi/np.sin(np.pi*p))*(np.pi/np.sin(np.pi*q))*np.exp(logbeta)*p**(-complex(s))*q**(-complex(t))*z**p*w**q
    return np.sum(integrand)*step**2/(2*np.pi)**2

def spectral():
    rows=[]
    # A full double-complex-order sample with unequal positive scales.
    s,t=mp.mpc('1.4','.2'),mp.mpc('2.1','-.15')
    b,N,z,w=.4,3.5,.7,1.3
    old=mp.mp.dps;mp.mp.dps=23
    nodes,weights=special.roots_legendre(260)
    lo,hi=-27.,27.
    direct=mp.mpc(0)
    for v,weight in zip(nodes,weights):
        y=mp.mpf(str((hi-lo)*v/2+(hi+lo)/2)); x=mp.exp(y)
        direct+=mp.mpf(str(weight))*(mp.exp(b*y)/(1+x)**N)*f(s,z*x)*f(t,w*x)
    direct*=(hi-lo)/2
    rhs=double_barnes(s,t,b,N,z,w)
    record(rows,'two complex orders, unequal scales: direct vs double Barnes',direct,mp.mpc(rhs),'2e-10')
    mp.mp.dps=old
    # Two elementary samples avoid sharing the polylogarithm evaluator.
    for b,N in ((.4,2.5),(-.5,1.7)):
        lhs=double_barnes(0,0,b,N,1,1)
        record(rows,f'double Barnes beta normalization b={b},N={N}',mp.mpc(lhs),mp.beta(b+2,N-b),'1e-10')
    return rows

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--part',choices=['all','kernels','moments','spectral','residues'],default='all');args=ap.parse_args()
    for part in (['kernels','moments','spectral','residues'] if args.part=='all' else [args.part]):
        started=time.time();rows=globals()[part]()
        result={'status':'PASS','part':part,'checks':rows,'count':len(rows),'mpmath_version':mp.__version__,
                'working_decimal_precision':40,'elapsed_seconds':round(time.time()-started,2),
                'scope':'Numerical diagnostics, not rigorous error enclosures. The spectral grid uses machine precision and its direct comparison uses 23 decimal digits.'}
        (ROOT/'results').mkdir(exist_ok=True)
        (ROOT/'results'/f'numeric_{part}.json').write_text(json.dumps(result,indent=2)+'\n')
        print(part, 'PASS',len(rows),'checks',flush=True)
if __name__=='__main__':main()
