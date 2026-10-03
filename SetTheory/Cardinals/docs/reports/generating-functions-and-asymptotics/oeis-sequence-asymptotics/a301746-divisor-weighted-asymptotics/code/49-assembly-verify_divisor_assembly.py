#!/usr/bin/env python3
"""Exact rational saddle coefficients, exact sequence recurrence, numerical checks.
No network, no external writes. Python 3 + sympy + mpmath.
"""
from pathlib import Path
import json, math, time
import sympy as s
import mpmath as mp
OUT=Path(__file__).resolve().parent
u,z=s.symbols('u z'); D=2*u+1

def coefficients(order=5):
    """R_j(u) in b_n = main * sum_j R_j(u)t^j, N=n-1/144."""
    K=2*order
    A=[s.Integer(0) for _ in range(K+1)]
    for j in range(3,K+3):
        A[j-2]+=(u+s.harmonic(j)-1)*z**j
    for p in range(3,order+1,2):
        c=-s.zeta(-p)**2/s.factorial(p)
        for r in range(p+1):
            if 2*p+r<=K:
                A[2*p+r]+=c*s.binomial(p,r)*(-z)**r
    E=[s.Integer(1)]
    for n in range(1,K+1):
        E.append(s.expand(sum(k*A[k]*E[n-k] for k in range(1,n+1))/n))
    R=[]
    for n in range(K+1):
        val=0
        for (p,),c in s.Poly(E[n],z).terms():
            if p%2==0:
                val+=c*(-1)**(p//2)*s.factorial2(p-1)/D**(p//2)
        val=s.factor(val)
        if n%2:
            assert val==0
        else:
            R.append(val)
    assert s.factor(R[1]+(36*u*u+72*u+47)/(24*D**3))==0
    # Independently assembled two-loop Gaussian correction.
    c={j:s.factorial(j)*(u+s.harmonic(j)-1) for j in range(2,7)}
    r2=-c[6]/(48*D**3)+35*c[4]**2/(384*D**4)+7*c[3]*c[5]/(48*D**4)-35*c[3]**2*c[4]/(64*D**5)+385*c[3]**4/(1152*D**6)
    assert s.factor(R[2]-r2)==0
    assert s.limit(R[3],u,s.oo)==-s.Rational(1,86400)
    return R

def divisors(M):
    d=[0]*(M+1)
    for k in range(1,M+1):
        for j in range(k,M+1,k):d[j]+=1
    return d

def exact_sequence(M,d):
    """Integer a_n recurrence: a_n=sum k*d(k)*(n-1)!/(n-k)! * a_(n-k)."""
    a=[1]
    for n in range(1,M+1):
        acc=0;fall=1
        for k in range(1,n+1):
            acc+=k*d[k]*fall*a[n-k]
            fall*=n-k
        a.append(acc)
    return a

def params(x):
    N=x-mp.mpf(1)/144
    U=mp.lambertw(2*N*mp.exp(2*mp.euler+2))/2
    T=mp.sqrt(U/N)
    return U,T

def logmain(x):
    U,T=params(x)
    return (2*U-1)/T+mp.mpf(1)/4+mp.mpf(3)/2*mp.log(T)-mp.log(2*mp.pi*(2*U+1))/2

def inverse0(y):
    X=y/mp.lambertw(y/mp.e); L=mp.log(X)
    U,T=params(X)
    simple=X-(2*U-1)/(T*L)+mp.mpf(1)/4
    def g(x):return mp.loggamma(x+1)-x*(mp.log(x)-1)+logmain(x)
    G=g(X);Gp=mp.digamma(X+1)-L+T-3*T*T/(2*(2*U+1))-T*T/(2*U+1)**2
    assert mp.almosteq(Gp,mp.diff(g,X))
    second=X-G/L+G*Gp/L**2-G**2/(2*X*L**3)
    return X,simple,second

def main():
    mp.mp.dps=90
    R=coefficients(5)
    (OUT/'coefficients.txt').write_text('\n'.join(f'R{j} = {q}\nlatex: {s.latex(q)}' for j,q in enumerate(R))+'\n')
    rf=[s.lambdify(u,r,'mpmath') for r in R]
    M=1200;d=divisors(M);a=exact_sequence(M,d)
    assert a[:11]==[1,1,5,25,193,1481,16021,167665,2220065,30004273,468585541]
    rows=[]
    for n in [25,50,100,200,400,800,1200]:
        U,T=params(n);ratio=mp.exp(mp.log(a[n])-mp.loggamma(n+1)-logmain(n))
        approx=mp.mpf(0); errors=[]
        for j in range(6):
            approx+=rf[j](U)*T**j
            errors.append(mp.nstr(ratio-approx,20))
        X,si,se=inverse0(mp.log(a[n]))
        rows.append(dict(n=n,u=mp.nstr(U,20),t=mp.nstr(T,20),main_relative_error=mp.nstr(ratio-1,20),expansion_residuals=errors,inverse_simple_error=mp.nstr(si-n,20),inverse_second_error=mp.nstr(se-n,20),inverse_second_scaled=mp.nstr((se-n)*mp.sqrt(X)*mp.log(X)**mp.mpf('1.5'),20)))
    # Direct positive series checks of Mellin residue signs.
    mellin=[]
    for tv in ['0.3','0.1','0.03']:
        T=mp.mpf(tv);K=int(mp.ceil(250/T));dd=divisors(K)
        L=mp.fsum(dd[k]*mp.exp(-k*T) for k in range(1,K+1))
        core=(mp.log(1/T)+mp.euler)/T+mp.mpf(1)/4-T/144-T**3/86400
        mellin.append(dict(t=tv,residual_over_t5=mp.nstr((L-core)/T**5,30),expected=str(-s.zeta(-5)**2/s.factorial(5))))
    report={'scope':'Exact integer coefficients through n=1200; symbolic Gaussian generator through t^5; numerical evidence, not proof.','coefficient_symbolic_checks':True,'numerics':rows,'mellin':mellin,'rational_coefficients':[str(q) for q in R]}
    (OUT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
