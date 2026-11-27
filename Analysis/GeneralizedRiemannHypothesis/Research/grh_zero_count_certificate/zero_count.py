#!/usr/bin/env python3
"""Rational-binomial count certificate. Exact arithmetic for rational inputs.
Optional --zeta: high-precision (NOT interval-certified) zeta illustration.
"""
from fractions import Fraction as Q
from math import comb, prod, ceil, floor
import argparse

def tail(n,k,t):
    if k <= 0: return t*0+1
    if k > n: return t*0
    return sum(comb(n,j)*t**j*(1-t)**(n-j) for j in range(k,n+1))

def nodes(n):
    return [Q(i,4*n**3) for i in range(1,n+1)]

def coeffs(ds,k):
    n=len(ds)
    return [tail(n,k,-1/d)/((-1/d)*prod(1-e/d for j,e in enumerate(ds) if j!=i))
            for i,d in enumerate(ds)]

def parameters(ds,tau,km,kp):
    n=len(ds)
    assert 0<tau<1 and 1<=km<=kp<=n
    assert all(d>0 for d in ds) and len(set(ds))==n
    return (coeffs(ds,km),coeffs(ds,kp),prod(1+d for d in ds),
            tail(n,km,tau),Q(n,kp)*tail(n-1,kp-1,tau))

def bracket(ds,tau,km,kp,M,values):
    """M=aF(a); values[i]=aF(a(1+ds[i])). Fractions in exact mode."""
    cm,cp,D,b,c=parameters(ds,tau,km,kp)
    return sum(x*y for x,y in zip(cp,values))-c*M, D*sum(x*y for x,y in zip(cm,values))/b

def bracket_intervals(ds,tau,km,kp,M,values):
    """Certified interval endpoints (lo,hi), all Fractions. M is nonnegative."""
    cm,cp,D,b,c=parameters(ds,tau,km,kp)
    def lin(cs, upper):
        return sum(co*v[int((co>=0)==upper)] for co,v in zip(cs,values))
    return lin(cp,False)-c*M[1], D*lin(cm,True)/b

def synthetic():
    for n,km,kp,tau,atoms in [
        (32,12,20,Q(1,2),[(Q(3,4),2),(Q(1,4),3),(Q(1,16),4)]),
        (64,25,39,Q(1,2),[(Q(1),3),(Q(4,5),4),(Q(1,5),5),(Q(1,100),40)]),
        (32,12,20,Q(1,2),[(Q(1,2),3),(Q(3,4),2),(Q(1,4),3)])]:
        ds=nodes(n)
        M=sum(t*m for t,m in atoms)
        vs=[sum(m*t/(1+d*t) for t,m in atoms) for d in ds]
        L,U=bracket(ds,tau,km,kp,M,vs)
        exact=sum(m for t,m in atoms if t>=tau)
        strict=sum(m for t,m in atoms if t>tau)
        assert L<=strict<=exact<=U
        for k in (km,kp):
            cs=coeffs(ds,k); t=Q(7,13)
            assert sum(c*t/(1+d*t) for c,d in zip(cs,ds)) == tail(n,k,t)/prod(1+d*t for d in ds)
        pad=Q(1,10**(15*n)); Ll,Uh=bracket_intervals(ds,tau,km,kp,(M-pad,M+pad),[(v-pad,v+pad) for v in vs])
        assert Ll<=L<=U<=Uh
        print(f'n={n}, strict={strict}, inclusive={exact}, exact bracket=[{float(L):.12f}, {float(U):.12f}], integer bracket=[{ceil(L)}, {floor(U)}]')

def zeta_demo(n=24,T=8):
    import mpmath as mp
    ds=nodes(n); tau=Q(1,2); km=ceil(Q(2,5)*n); kp=ceil(Q(3,5)*n)
    cm,cp,D,b,c=parameters(ds,tau,km,kp)
    maxcoef=max(abs(x) for x in cm+cp)
    digits=max(80,len(str(maxcoef.numerator))-len(str(maxcoef.denominator))+70)
    def run(dps):
        with mp.workdps(dps):
            def m(q): return mp.mpf(q.numerator)/q.denominator
            a=mp.mpf(T)**2
            def F(x):
                s=mp.mpf('0.5')+mp.sqrt(x)
                return (1/s+1/(s-1)-mp.log(mp.pi)/2+mp.digamma(s/2)/2+mp.zeta(s,derivative=1)/mp.zeta(s))/mp.sqrt(x)
            M=a*F(a); vs=[a*F(a*(1+m(d))) for d in ds]
            L=mp.fsum(m(x)*y for x,y in zip(cp,vs))-m(c)*M
            U=m(D)*mp.fsum(m(x)*y for x,y in zip(cm,vs))/m(b)
            return mp.nstr(L,18),mp.nstr(U,18)
    r1=run(digits); r2=run(digits+30)
    print(f'zeta, T={T}, n={n}, dps={digits}/{digits+30}, approximate bracket={r2}, stable={r1==r2}; NOT rigorous interval arithmetic')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--zeta',action='store_true');p.add_argument('--n',type=int,default=24);p.add_argument('--T',type=int,default=8);args=p.parse_args()
    synthetic()
    if args.zeta: zeta_demo(args.n,args.T)
