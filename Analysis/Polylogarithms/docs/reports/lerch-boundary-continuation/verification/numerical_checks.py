#!/usr/bin/env python3
"""Independent high-precision diagnostics; these are not proof certificates.
Requires mpmath. Modes: identity, roots, fold, minimum. Outputs JSON in ../data.
"""
from __future__ import annotations
from argparse import ArgumentParser
from pathlib import Path
from math import factorial,comb
import json
import mpmath as mp
from certify import elementary,polynomial

OUT=Path(__file__).resolve().parent.parent/'data'

def mq(q):return mp.mpf(q.numerator)/q.denominator

def zjet(j,s,a=1):
    return mp.zeta(s,a) if j==0 else mp.diff(lambda z:mp.zeta(z,a),s,j)

def C(n,k,r,a=1):
    return factorial(k)*sum(mq(e)*factorial(n)/factorial(n-i)*zjet(n-i,k+1-r,a)
                            for i,e in enumerate(elementary(k)[:n+1]))

def A(n,k,a=1):
    es=elementary(k)
    ans=mp.mpf(factorial(n))*mq(es[n+1]) if n+1<=k else mp.mpf(0)
    for i,e in enumerate(es[:n+1]):
        ans+=mq(e)*factorial(n)/factorial(n-i)*(-1)**(n-i)*mp.stieltjes(n-i,a)
    return ans

def gamma_moment(n,L):
    R=[mp.mpf(1)]
    for m in range(n):
        R.append((L+mp.euler)*R[m]+sum(comb(m,r)*factorial(r)*mp.zeta(r+1)*R[m-r] for r in range(1,m+1)))
    return R[n]

def direct(n,k,a,eta):
    rho=mp.exp(-eta);p=mp.mpf(1);v=mp.mpf(0)
    coeffs=[mq(x) for x in polynomial(n,k)]
    M=int(mp.ceil((mp.mp.dps+18)*mp.log(10)/eta))
    for m in range(M):
        x=a+m;L=-mp.log(x)
        v+=p*factorial(k)*mp.polyval(list(reversed(coeffs)),L)/x**(k+1)
        p*=rho
    return v,M

def identities():
    rows=[]
    for n,k,et in [(0,1,'0.3'),(1,1,'0.2'),(2,1,'0.1'),(3,1,'0.1'),(2,2,'0.1'),(2,3,'0.1')]:
        eta=mp.mpf(et);a=mp.mpf(1);R=32
        lhs,M=direct(n,k,a,eta)
        rhs=mp.exp(a*eta)*(sum((-eta)**r/mp.factorial(r)*C(n,k,r,a) for r in range(R+1) if r!=k)
               +(-eta)**k*(A(n,k,a)-gamma_moment(n+1,mp.log(eta))/(n+1)))
        residual=lhs-rhs
        assert abs(residual)<mp.mpf('1e-32'),(n,k,residual)
        row={'n':n,'k':k,'a':'1','eta':et,'spectral_terms':M,'Abel_cutoff':R,
             'residual':mp.nstr(residual,15),'status':'non-interval high-precision diagnostic'}
        rows.append(row);print(row,flush=True)
    return rows

def bracketed_newton(f, df, left, right):
    """Safeguarded Newton iteration; never permit a root to leave its bracket."""
    left,right=mp.mpf(str(left)),mp.mpf(str(right))
    fl,fr=f(left),f(right)
    if fl*fr >= 0:
        raise ValueError("The supplied interval must have opposite endpoint signs")
    x=(left+right)/2
    tol=mp.power(10,-mp.mp.dps+8)
    for _ in range(160):
        fx=f(x)
        if abs(fx)<tol:
            return x
        if fl*fx<0:
            right,fr=x,fx
        else:
            left,fl=x,fx
        slope=df(x)
        candidate=x-fx/slope if slope else (left+right)/2
        x=candidate if left<candidate<right else (left+right)/2
    raise ArithmeticError("Bracketed iteration did not converge")

def roots():
    intervals={1:[(1,1.5)],2:[(1,1.3),(1.3,2)],
               3:[(.8,1.1),(1.1,1.5),(1.5,2.1)],
               4:[(.8,.94),(.94,1.2),(1.2,1.7),(1.7,2.2)]}
    rows=[]
    for n,ivs in intervals.items():
        for j,iv in enumerate(ivs,1):
            a=bracketed_newton(lambda a:C(n,1,0,a),lambda a:-C(n,2,0,a),*iv)
            assert mp.mpf(str(iv[0]))<a<mp.mpf(str(iv[1]))
            fa=-C(n,2,0,a)
            assert mp.sign(fa)==(-1)**j, "Wrong crossing direction" 
            if j>1:
                assert a>mp.mpf(rows[-1]['a_endpoint'])

            coeff=(-1)**(n+1)/((n+1)*fa)
            rows.append({'n':n,'j':j,'a_endpoint':mp.nstr(a,32),
                         'F_a':mp.nstr(fa,30),'leading_rho_derivative_coefficient':mp.nstr(coeff,30)})
            print(rows[-1],flush=True)
    return rows

def integral3(a,u,j=0,r=0):
    eta=mp.exp(-u);rho=mp.exp(-eta)
    def f(x):
        if not x:return mp.mpf(0)
        y=mp.log(x)+mp.euler
        den=-mp.expm1(-eta-x)
        return (-1)**j*factorial(r)*x**(1+j)*mp.exp(-(a+r)*x)/den**(1+r)*(y**3-3*mp.zeta(2)*y+2*mp.zeta(3))
    return mp.quad(f,[0,eta,mp.sqrt(eta),mp.mpf('.1'),1,10,mp.inf])

def fold():
    # u = -log(eta), rho=exp(-eta). Independent Laplace-integral engine.
    a,u=mp.findroot(lambda a,u:(integral3(a,u),integral3(a,u,j=1)),
                    (mp.mpf('1.04975'),mp.mpf('11.5607')),tol=mp.mpf('1e-24'))
    rho=mp.exp(-mp.exp(-u));faa=integral3(a,u,j=2);fr=integral3(a,u,r=1)
    return {'a_c':mp.nstr(a,26),'rho_c':mp.nstr(rho,26),'F_aa':mp.nstr(faa,20),
            'F_rho':mp.nstr(fr,20),'square_root_coefficient':mp.nstr(mp.sqrt(-2*fr/faa),20),
            'status':'non-interval numerical location; existence/uniqueness in the inner gap proved analytically'}

def minimum():
    def fun(a,rho):
        F=Fr=Fa=Frr=mp.mpf(0);p=mp.mpf(1)
        for m in range(1600):
            x=a+m;l=mp.log(x);f=l*(l-2)/x**2
            F+=p*f;Fr+=m*p*f/rho;Fa+=p*(-2*l*l+6*l-2)/x**3
            Frr+=m*(m-1)*p*f/rho**2;p*=rho
        return F,Fr,Fa,Frr
    a,rho=mp.findroot(lambda a,r:fun(a,r)[:2],(mp.mpf('.8786'),mp.mpf('.9156')))
    vals=fun(a,rho)
    return {'a_min':mp.nstr(a,35),'rho_min':mp.nstr(rho,35),
            'F_a':mp.nstr(vals[2],30),'F_rho_rho':mp.nstr(vals[3],30),
            'status':'diagnostic decimals; separate exact certificate brackets rho_min'}

if __name__=='__main__':
    p=ArgumentParser();p.add_argument('mode',choices=['identity','roots','fold','minimum']);p.add_argument('--dps',type=int,default=45)
    args=p.parse_args();mp.mp.dps=args.dps
    data={'precision_dps':args.dps,'results':{'identity':identities,'roots':roots,'fold':fold,'minimum':minimum}[args.mode]()}
    OUT.mkdir(exist_ok=True);(OUT/f'numerical_{args.mode}.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))
