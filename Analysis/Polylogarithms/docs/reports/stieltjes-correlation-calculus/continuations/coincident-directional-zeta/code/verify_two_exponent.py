#!/usr/bin/env python3
"""Reproducible diagnostics for the two-exponent Laurent formula.

The closed-form prediction uses the finite residue convolution P_m.
The scalar continuation independently retains the original first N terms
of the nested Hurwitz-zeta sum and appends a long Euler--Maclaurin tail.
A discrete Cauchy average extracts each Laurent coefficient without
subtracting the predicted principal part. Results are floating-point
diagnostics, not interval certificates and not the proof.
"""
from pathlib import Path
from functools import lru_cache
import json
import argparse
import time
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]

def mul(a,b,R):
    z=[0]*(R+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j<=R: z[i+j]+=x*y
    return z

@lru_cache(None)
def q_exact(L,R):
    logs=[[sp.S.Zero]*(R+1) for _ in range(L+1)]
    for k in range(1,L+1):
        for d in range(1,min(R,k+1)+1):
            logs[k][d]=(-1)**(k+1)*sp.binomial(k+1,d)*sp.bernoulli(k+1-d,0)/(k*(k+1))
    q=[[sp.S.One]+[sp.S.Zero]*R]
    for n in range(1,L+1):
        v=[sp.S.Zero]*(R+1)
        for k in range(1,n+1):
            c=mul(logs[k],q[n-k],R)
            for d in range(R+1):v[d]+=k*c[d]/n
        q.append([sp.cancel(x) for x in v])
    return q

def mpq(x):
    return mp.mpf(int(sp.numer(x)))/mp.mpf(int(sp.denom(x)))

def Ccoeff(a,R):
    c=[mp.mpf(1)]+[mp.mpf(0)]*R
    logs=[mp.mpf(0)]+[-mp.polygamma(k-1,a)/mp.factorial(k) for k in range(1,R+1)]
    for n in range(1,R+1):
        c[n]=sum(k*logs[k]*c[n-k] for k in range(1,n+1))/n
    return c

def A(k,s):
    if k==0:return 1/(s-1)
    if k==1:return -mp.mpf('0.5')
    if k%2:return mp.mpf(0)
    return mp.bernoulli(k)*mp.rf(s,k-1)/mp.factorial(k)

def scalar(s,t,a,r,N=72,L=34):
    # Directly retain the original nested-sum coefficients.
    ee=[mp.mpf(1)]+[mp.mpf(0)]*r
    out=mp.mpc(0)
    for n in range(N):
        x=n+a
        out+=ee[r]*mp.power(x,-t)*mp.zeta(s,x+1)
        for d in range(r,0,-1):ee[d]+=ee[d-1]/x
    qs=[[mpq(x) for x in row] for row in q_exact(L-1,r)]
    cs=Ccoeff(a,r)
    qs=[mul(cs,row,r) for row in qs]
    aa=[A(k,s) for k in range(L)]
    for ell in range(L):
        dd=[sum(qs[j][d]*aa[ell-j] for j in range(ell+1)) for d in range(r+1)]
        w=s+t-1+ell
        for d in range(r+1):
            order=r-d
            out+=dd[d]*(-1)**order*mp.zeta(w,N+a,derivative=order)/mp.factorial(order)
    return out

def exact_prediction(m,r,a,alpha,beta):
    u=sp.Symbol('u')
    sig=sp.Symbol('sigma')
    theta=sp.Rational(alpha)/sp.Rational(alpha+beta)
    qs=q_exact(m+1,r+1)
    pols=[sum(v*u**d for d,v in enumerate(row)) for row in qs]
    def As(k):
        if k==0:return 1/(sig-1)
        if k==1:return -sp.Rational(1,2)
        if k%2:return sp.S.Zero
        return sp.bernoulli(k,0)*sp.rf(sig,k-1)/sp.factorial(k)
    p=sum(pols[j]*As(m+1-j) for j in range(m+2))
    pp=sp.series(p.subs(sig,-m+theta*u),u,0,r+2).removeO().expand()
    vv=mul(Ccoeff(a,r+1),[mpq(pp.coeff(u,d)) for d in range(r+2)],r+1)
    delta=mp.mpf(0)
    for j in range(1,m+2):
        fall=mp.mpf(1)
        for k in range(j):fall*=a-1-k
        delta+=(-1)**(r+2)*int(sp.functions.combinatorial.numbers.stirling(m+1,j,kind=2))*fall/mp.mpf(j)**(r+2)
    q=mp.mpf(alpha+beta)
    ans={str(-h):vv[r+1-h]/q**h for h in range(r+2)}
    ans['0']+=delta
    return ans

def contour(m,r,a,alpha,beta,N,L,points=24,radius='0.01'):
    radius=mp.mpf(radius)
    sums={str(-h):mp.mpc(0) for h in range(r+2)}
    for k in range(points):
        eps=radius*mp.exp(2j*mp.pi*(k+mp.mpf('.375'))/points)
        val=scalar(-m+alpha*eps,1+beta*eps,a,r,N,L)
        for h in range(r+2):sums[str(-h)]+=val*eps**h/points
    return sums

def symbolic_checks():
    u,z,s,theta=sp.symbols('u z s theta')
    out=[]
    for m in range(7):
        qs=q_exact(m+1,2*(m+1))
        ps=[sum(v*u**j for j,v in enumerate(row)) for row in qs]
        def aa(k):
            if k==0:return 1/(s-1)
            if k==1:return -sp.Rational(1,2)
            if k%2:return 0
            return sp.bernoulli(k,0)*sp.rf(s,k-1)/sp.factorial(k)
        p=sum(ps[j]*aa(m+1-j) for j in range(m+2))
        kernel=sp.exp(-z)*sp.exp((1+u)*sp.log(z/(1-sp.exp(-z))))
        # A finite local expansion is enough, and avoids enormous expressions.
        bk=sp.series(kernel,z,0,m+2).removeO().expand().coeff(z,m+1)
        w=sp.rf(u-m,m+1)*bk
        residue=sp.cancel(u*p.subs(s,-m+u)-w)
        out.append({'m':m,'identity_uP_equals_W':str(residue),'pass':residue==0})
    return out

def run(quick=False):
    mp.mp.dps=65
    cases=[(0,0,'0.7',1,2),(0,1,'0.5',1,2),(1,0,'1.3',2,-1),(1,1,'0.5',1,1),(2,1,'0.5',2,1),(3,0,'1.25',1,3),(0,2,'1.25',1,1),(2,0,'0.7',1,1)]
    if quick:cases=cases[:2]
    rows=[]
    for idx,(m,r,astr,alpha,beta) in enumerate(cases):
        a=mp.mpf(astr)
        pred=exact_prediction(m,r,a,alpha,beta)
        obs=contour(m,r,a,alpha,beta,64,32,points=20 if quick else 32)
        residuals={h:abs(obs[h]-v) for h,v in pred.items()}
        row={'m':m,'trailing_depth':r,'a':astr,'alpha':alpha,'beta':beta,
             'predicted':{h:mp.nstr(v,55) for h,v in pred.items()},
             'observed':{h:mp.nstr(v,55) for h,v in obs.items()},
             'absolute_errors':{h:mp.nstr(v,8) for h,v in residuals.items()}}
        rows.append(row)
        print('case',idx+1,'max error',mp.nstr(max(residuals.values()),8),flush=True)
    # Independent tail-depth/cutoff repeat on a case with a genuine nonzero principal part.
    m,r,astr,alpha,beta=cases[-1]
    a=mp.mpf(astr)
    eps=mp.mpc('.012','.007')
    x=scalar(-m+alpha*eps,1+beta*eps,a,r,64,32)
    y=scalar(-m+alpha*eps,1+beta*eps,a,r,88,40)
    stability=mp.nstr(abs(x-y),8)
    print('tail repeat',stability,flush=True)
    report={'working_precision_decimal':mp.mp.dps,'software':{'mpmath':mp.__version__,'sympy':sp.__version__},'initial_cutoff':64,'tail_terms':32,'cauchy_points':20 if quick else 32,'cauchy_radius':'0.01','repeat_cutoff':88,'repeat_tail_terms':40,'method':'Original nested-sum partial sum plus Euler--Maclaurin asymptotic tail; discrete Cauchy Laurent extraction','rigorous_certificate':False,'cases':rows,'tail_repeat_difference':stability,'symbolic_checks':symbolic_checks()}
    (ROOT/'results'/'two_exponent_verification.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--quick',action='store_true');args=parser.parse_args()
    run(args.quick)
