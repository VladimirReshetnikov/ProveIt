#!/usr/bin/env python3
"""Independent numerical diagnostics. None of this script's decimals is a proof.

Requires mpmath. Exact proof-bearing sign decisions are in certify.py instead.
"""
from __future__ import annotations
from pathlib import Path
from functools import lru_cache
import argparse
import json
import mpmath as mp
from numeric_em import F_all, rising, mul

@lru_cache(maxsize=None)
def qcoeff(n:int):
    # q_n(x) = sum_{j=0}^n binom(n,j) [d^j (1/Gamma(1+t))]_{t=0} x^(n-j)
    rg=mp.taylor(lambda t:1/mp.gamma(1+t),0,n)
    return [mp.factorial(n)*rg[n-j]/mp.factorial(j) for j in range(n+1)]

def Q(n,x):return mp.polyval(list(reversed(qcoeff(n))),x)

def integral_F(n,k,a,rho,dr=0):
    def f(x):
        den=(1-rho)+rho*(-mp.expm1(-x))
        return mp.factorial(dr)*x**k*mp.exp(-(a+dr)*x)*Q(n,mp.log(x))/den**(dr+1)
    return mp.quad(f,[0,mp.mpf('.05'),mp.mpf('.2'),1,3,10,mp.inf])

def elementary_F(n,k,a):
    p=rising(1,k,n)
    return mp.factorial(n)*sum(p[j]*(-mp.log(a))**(n-j)/mp.factorial(n-j) for j in range(n+1))/a**(k+1)

def direct_F(n,k,a,rho):
    if rho==0:return elementary_F(n,k,a)
    if rho==1:return F_all(k,a,n,N=40,M=20)[n]
    return mp.fsum(rho**m*elementary_F(n,k,a+m) for m in range(190))

@lru_cache(maxsize=None)
def gamma_coeff(n:int):return tuple(mp.taylor(lambda t:mp.gamma(1-t),0,n))

def R(n:int,x):
    g=gamma_coeff(n)
    return mp.factorial(n)*sum(g[j]*x**(n-j)/mp.factorial(n-j) for j in range(n+1))

def C(n,k,a):
    p=rising(1,k,n+1)
    pk=[p[j]/mp.factorial(k) for j in range(n+2)]
    return mp.factorial(n)*pk[n+1]+sum(mp.factorial(n)*pk[j]*(-1)**(n-j)*mp.stieltjes(n-j,a)/mp.factorial(n-j) for j in range(n+1))

def main(out:Path,full:bool):
    mp.mp.dps=40
    out.mkdir(parents=True,exist_ok=True)
    checks=[]
    for n in range(6):
      for k in (1,2,3):
       for a in (mp.mpf('.7'),mp.mpf('1.3')):
        for rho in (mp.mpf(0),mp.mpf('.5'),mp.mpf(1)):
            x=integral_F(n,k,a,rho);y=direct_F(n,k,a,rho)
            err=abs(x-y)/max(1,abs(x),abs(y))
            assert err<mp.mpf('1e-27'),(n,k,a,rho,err)
            checks.append({'n':n,'k':k,'a':str(a),'rho':str(rho),'relative_scaled_error':str(err)})
    print('Integral/series comparisons:',len(checks),flush=True)
    endpoint=[]
    a=mp.mpf('1.3')
    for n in range(5):
        f1=F_all(1,a,n,N=40,M=20)[n];cn=C(n,1,a)
        z0=mp.diff(lambda s:mp.zeta(s,a),0,n)
        if n:z0+=n*mp.diff(lambda s:mp.zeta(s,a),0,n-1)
        target=z0/2
        for mus in ('1e-3','1e-6','1e-9'):
            mu=mp.mpf(mus);rho=mp.exp(-mu)
            observed=mp.exp(-a*mu)*integral_F(n,1,a,rho)
            residual=(observed-f1-mu*(R(n+1,mp.log(mu))/(n+1)-cn))/mu**2
            endpoint.append({'n':n,'mu':str(mu),'residual_over_mu_squared':str(residual),'predicted_limit':str(target)})
    print('Endpoint expansion diagnostics:',len(endpoint),flush=True)
    # Compare the a=1 specialization with order derivatives of Li_s.
    polychecks=[]
    rho=mp.exp(mp.mpf('-.2'))
    for n in range(4):
        value=mp.diff(lambda s:mp.polylog(s,rho),2,n)
        if n:value+=n*mp.diff(lambda s:mp.polylog(s,rho),2,n-1)
        expected=rho*integral_F(n,1,1,rho)
        err=abs(value-expected)
        assert err<mp.mpf('1e-27')
        polychecks.append({'n':n,'absolute_error':str(err)})
    output={'status':'numerical diagnostics only; not certificates',
            'dps':mp.mp.dps,'integral_comparison_count':len(checks),
            'integral_comparisons':checks,'endpoint_diagnostics':endpoint,
            'polylog_order_derivative_comparisons':polychecks}
    if full:
        a,rho=mp.findroot(lambda a,r:(integral_F(2,1,a,r),integral_F(2,1,a,r,1)),(.88,.92),tol=mp.mpf('1e-28'))
        output['n2_minimum']={'a':str(a),'rho':str(rho)}
        af,u=mp.findroot(lambda a,u:(integral_F(3,1,a,mp.exp(-mp.exp(u))),integral_F(3,2,a,mp.exp(-mp.exp(u)))),
                         (1.05,mp.log(mp.mpf('1e-5'))),tol=mp.mpf('1e-27'))
        rf=mp.exp(-mp.exp(u))
        output['n3_left_fold']={'a':str(af),'rho':str(rf),'F_rho':str(integral_F(3,1,af,rf,1)),
                                'F_aa':str(integral_F(3,3,af,rf))}
    (out/'numerical_diagnostics.json').write_text(json.dumps(output,indent=2)+'\n')
    print('Polylog comparisons:',len(polychecks),flush=True)
    if full:print(json.dumps({k:v for k,v in output.items() if k in ('n2_minimum','n3_left_fold')},indent=2),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,default=Path(__file__).resolve().parents[1]/'certificates')
    ap.add_argument('--full',action='store_true',help='also recompute the two two-variable critical points')
    args=ap.parse_args();main(args.out,args.full)
