#!/usr/bin/env python3
"""Exact polynomial Airy recursion for fixed-d combining networks.

F''=(c*x+ell)*F, c=2*(d-1)/(d+1), F(0)=0, F'(0)=1.  All pairs (P,Q) mean
P(x)*F(x)+Q(x)*F'(x).  No Airy integral or numerical fit is used.
"""
from pathlib import Path
import argparse
import json
import os
degree=int(os.environ.get("COMBINING_D", "3"))
import sympy as s

x,e,ell=s.symbols('x e ell')
c=s.Rational(2*(degree-1),degree+1)
V=c*x+ell
ZERO=(s.S.Zero,s.S.Zero)
def add(u,v): return tuple(s.expand(u[i]+v[i]) for i in (0,1))
def mul(a,u): return tuple(s.expand(a*p) for p in u)
def D(u): return (s.expand(s.diff(u[0],x)+V*u[1]),s.expand(u[0]+s.diff(u[1],x)))
def L(u): return add(D(D(u)),mul(-V,u))
def trunc(a,n):
    if n<0: return s.S.Zero
    return s.series(a,e,0,n+1).removeO().expand()
def shift(u,y,n):
    delta=trunc(y-x,n); ans=ZERO; du=u
    for j in range(n+1):
        ans=add(ans,mul(trunc(delta**j/s.factorial(j),n),du))
        du=D(du)
    return tuple(trunc(p,n) for p in ans)
def poly_solve(R,S):
    """Unique polynomial inverse of L, apart from the free multiple of F."""
    T=s.expand(R-s.diff(S,x)/2); Q=s.S.Zero
    while T!=0:
        d=s.degree(T,x)
        a=s.expand(T).coeff(x,d)/(c*(2*d+1))
        q=a*x**d
        Q+=q
        T=s.expand(T-(-s.diff(q,x,3)/2+2*V*s.diff(q,x)+c*q))
    P=s.integrate((S-s.diff(Q,x,2))/2,x)
    P=s.expand(P-P.subs(x,0)-s.diff(Q,x).subs(x,0))
    assert all(s.expand(z)==0 for z in add(L((P,Q)),(-R,-S)))
    return P,s.expand(Q)

def residual(kind,Fs,coeff,m):
    raw=s.prod(1-2*(x*e**2+(h-1)*e**3)/((degree+1)*(1+x*e**2-e**3)) for h in range(1,degree))
    u=trunc(raw,m)
    if kind=='frozen':
        um=trunc(s.sqrt(raw),m)
        up=trunc(s.sqrt(raw.subs(x,x+e)),m)
        ym,yp=x-e,x+e
    else:
        um,up=u,s.S.One
        ym=trunc((x-e)*(1-e**3)**(-s.Rational(1,3)),m)
        yp=trunc((x+e)*(1-e**3)**(-s.Rational(1,3)),m)
    rhs=ZERO
    for k,F in enumerate(Fs):
        if k>m: break
        inside=add(mul(um,shift(F,ym,m-k)),mul(up,shift(F,yp,m-k)))
        time=trunc((1-e**3)**(-s.Rational(k,3)),m-k) if kind=='nonautonomous' else s.S.One
        rhs=add(rhs,mul(e**k*time,inside))
    scalar=2+sum(v*e**j for j,v in coeff.items())
    # Both modes store the full scalar coefficients: lambda_m or 2*s_m.
    lhs=mul(scalar,tuple(sum(e**k*F[i] for k,F in enumerate(Fs)) for i in (0,1)))
    return add(rhs,mul(-1,lhs))

def derive(kind,n):
    Fs=[(s.S.One,s.S.Zero)]; coeff={2:ell}
    for m in range(3,n+1):
        R,S=[s.expand(p).coeff(e,m) for p in residual(kind,Fs,coeff,m)]
        P,Q=poly_solve(-R,-S)
        mu=s.factor(-c*Q.subs(x,0))
        Q=s.expand(Q+mu/c)
        G=(s.factor(P),s.factor(Q))
        assert G[1].subs(x,0)==0
        assert s.simplify(G[0].subs(x,0)+s.diff(G[1],x).subs(x,0))==0
        assert all(s.expand(z)==0 for z in add(add(L(G),(-mu,0)),(R,S)))
        coeff[m]=mu; Fs.append(G)
        print(kind,'order',m,'lambda' if kind=='frozen' else 's',s.factor(mu if kind=='frozen' else mu/2),'profile',G,flush=True)
    rr=residual(kind,Fs,coeff,n)
    checks={str(m):all(s.expand(p).coeff(e,m)==0 for p in rr) for m in range(n+1)}
    assert all(checks.values())
    return Fs,coeff,checks

def endpoint(Fs,n):
    # The exact Taylor recursion for F(0)=0, F'(0)=1.
    f=[s.S.Zero,s.S.One]
    for j in range(2,n+4):
        f.append(s.expand((ell*f[j-2]+(c*f[j-3] if j>=3 else 0))/(j*(j-1))))
    F=sum(a*x**j for j,a in enumerate(f)); Fp=s.diff(F,x)
    return trunc(sum(e**k*(P*F+Q*Fp).subs(x,e) for k,(P,Q) in enumerate(Fs))/e,n)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--order',type=int,default=6);args=ap.parse_args()
    n=args.order;data={}
    for kind in ('frozen','nonautonomous'):
        Fs,coeff,checks=derive(kind,n)
        end=endpoint(Fs,n-3)
        print(kind,'endpoint/epsilon',end,flush=True)
        data[kind]={'scalar_coefficients':{str(k):str(v) for k,v in coeff.items()},'profiles':[[str(p),str(q)] for p,q in Fs],'residual_zero_through':checks,'endpoint_over_e':str(end)}
        if kind=='nonautonomous':
            ss={k:v/2 for k,v in coeff.items()};rho=ss[3]
            hh=s.symbols('h1:'+str(n-2))
            # log H_N = N log 2 + 3*s2*N^(1/3)+rho log N + sum h_j*N^(-j/3).
            lr=3*ss[2]/e*(1-(1-e**3)**s.Rational(1,3))-rho*s.log(1-e**3)
            lr+=sum(h*e**j*(1-(1-e**3)**(-s.Rational(j,3))) for j,h in enumerate(hh,1))
            target=trunc(s.log(1+sum(v*e**k for k,v in ss.items())),n)
            diff=trunc(lr-target,n)
            sol=s.solve([diff.coeff(e,k) for k in range(4,n+1)],hh,dict=True)[0]
            sol={k:s.factor(v) for k,v in sol.items()}
            logend=trunc(s.log(end),n-3)
            logs=[s.factor(sol[h]+logend.coeff(e,k)) for k,h in enumerate(hh,1)]
            # N=2*n. In terms of the Airy root z, ell=z*c^(2/3).
            z=s.symbols('z')
            logsn=[s.simplify(v.subs(ell,z*c**s.Rational(2,3))/2**s.Rational(k,3)) for k,v in enumerate(logs,1)]
            print('nonautonomous logH',sol,flush=True)
            print('nonautonomous logforward_N',logs,flush=True)
            print('nonautonomous logforward_n',logsn,flush=True)
            data[kind].update(s_coefficients={str(k):str(v) for k,v in ss.items()},logH={str(k):str(v) for k,v in sol.items()},logforward_N=list(map(str,logs)),logforward_n=list(map(str,logsn)))
    Path(__file__).with_name('coefficients-d%d.json'%degree).write_text(json.dumps(data,indent=2)+'\n')

if __name__=='__main__': main()
