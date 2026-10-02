#!/usr/bin/env python3
"""Exact distinct-partition polynomials and moving-fugacity Bessel models."""
import argparse, json, math
from fractions import Fraction
from functools import lru_cache
import mpmath as mp
import sympy as sp

@lru_cache(None)
def c_symbolic(j):
    u=sp.Symbol('u', positive=True)
    f=sp.log(1+u)
    for _ in range(2*j-1):
        f=sp.cancel(u*sp.diff(f,u))
    return sp.factor(sp.bernoulli(2*j)*f/sp.factorial(2*j))

@lru_cache(None)
def c_function(j):
    u=sp.Symbol('u', positive=True)
    return sp.lambdify(u,c_symbolic(j),'mpmath')

def h_coefficients(u, M):
    # H(z)=exp(sum_{j>=2} c_j z^(2j-1)); m*h_m=sum d*g_d*h_(m-d).
    g=[mp.mpf('0')]*(M+1)
    for j in range(2,(M+1)//2+1):
        d=2*j-1
        if d<=M: g[d]=c_function(j)(u)
    h=[mp.mpf('1')]+[mp.mpf('0')]*M
    for m in range(1,M+1):
        h[m]=sum(d*g[d]*h[m-d] for d in range(1,m+1))/m
    return h

def parameters(x, alpha):
    x,alpha=mp.mpf(x),mp.mpf(alpha)
    u=x**alpha
    A=-mp.polylog(2,-u)
    N=x+u/(12*(1+u))
    t=mp.sqrt(A/N); s=mp.sqrt(A*N)
    return u,A,N,t,s

def log_model(x, alpha, M=0):
    u,A,N,t,s=parameters(x,alpha)
    h=h_coefficients(u,M)
    summation=sum(h[m]*t**m*mp.besseli(m+1,2*s)/mp.besseli(1,2*s)
                  for m in range(M+1))
    return -mp.log1p(u)/2+mp.log(t)+mp.log(mp.besseli(1,2*s))+mp.log(summation)

def log_oeis_equivalent(x,alpha):
    x,alpha=mp.mpf(x),mp.mpf(alpha)
    A=alpha**2*mp.log(x)**2/2+mp.pi**2/6
    return 2*mp.sqrt(A*x)+mp.log(A)/4-(alpha/2+mp.mpf(3)/4)*mp.log(x)-mp.log(2*mp.sqrt(mp.pi))

def exact_polynomials(targets):
    """p[n,m] for selected n: p[n,m]=[q^(n-m(m+1)/2)]prod_(j<=m)(1-q^j)^-1."""
    N=max(targets)
    p=[0]*(N+1);p[0]=1
    out={n:[0] for n in targets}
    for m in range(1,(math.isqrt(8*N+1)-1)//2+1):
        for k in range(m,N+1):p[k]+=p[k-m]
        tri=m*(m+1)//2
        for n in targets:
            if tri<=n:out[n].append(p[n-tri])
    return out

def exact_value(coeffs,u):
    out=0
    for a in reversed(coeffs):out=out*u+a
    return out

def log_sector_model(x, alpha, M=9, K=0):
    """Finite conjugate-sector approximant; only fixed K has the proved asymptotic scope."""
    u,A,N,t,s=parameters(x,alpha)
    h=h_coefficients(u,M); total=mp.mpf(0)
    for j in range(K+1):
        Aj=A-2*mp.pi**2*j*j+2j*mp.pi*j*mp.log(u)
        tj=mp.sqrt(Aj/N);sj=mp.sqrt(N*Aj)
        value=(-1)**j*sum(h[m]*tj**(m+1)*mp.besseli(m+1,2*sj) for m in range(M+1))
        total+=mp.re(value) if j==0 else 2*mp.re(value)
    if total<=0:
        raise ValueError("Finite-sector model is not positive at this input; asymptotic regime required")
    return mp.log(total)-mp.log1p(u)/2

def inverse(y,alpha,M=9,K=0):
    """Solve the positive smooth M-term Bessel model; y is log target."""
    y,alpha=mp.mpf(y),mp.mpf(alpha)
    z=y/(2*mp.sqrt(2)*alpha)
    r=z/mp.lambertw(z)
    x=r*r
    for j in range(30):
        f=log_sector_model(x,alpha,M,K)-y
        step=f/mp.diff(lambda xx:log_sector_model(xx,alpha,M,K),x)
        x-=step
        if abs(step)<mp.eps**mp.mpf('.7')*x:break
    return x

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-n',type=int,default=20000);ap.add_argument('--output',default='checks.json');args=ap.parse_args()
    mp.mp.dps=100
    targets=sorted(set([n for n in [10,20,50,100,200,500,1000,2000,5000,10000,20000,args.max_n] if n<=args.max_n]))
    poly=exact_polynomials(targets)
    rows=[]
    for alpha in [mp.mpf('.25'),mp.mpf('.5'),1,2]:
        for n in targets:
            u=mp.mpf(n)**alpha
            exact=exact_value(poly[n],n**alpha if isinstance(alpha,int) else u)
            le=mp.log(exact)
            row={'alpha':str(alpha),'n':n,'log_exact':mp.nstr(le,35)}
            for M in [0,3,5,9]:
                row['relative_error_M'+str(M)]=mp.nstr(mp.expm1(log_model(n,alpha,M)-le),16)
            row['relative_error_oeis_form']=mp.nstr(mp.expm1(log_oeis_equivalent(n,alpha)-le),16)
            u,A,N,t,s=parameters(n,alpha)
            row['M0_scaled_error']=mp.nstr((mp.expm1(log_model(n,alpha,0)-le))/(t**3/u),16)
            rows.append(row)
    # Exact low terms check the two named sequences.
    low=exact_polynomials(list(range(1,24)))
    low1=[1]+[exact_value(low[n],n) for n in range(1,24)]
    low2=[1]+[exact_value(low[n],n*n) for n in range(1,24)]
    out={'c_j':{str(j):str(c_symbolic(j)) for j in range(1,7)},'low_alpha1':low1,'low_alpha2':low2,'rows':rows,'inverse_checks':[]}
    for alpha in [1,2]:
        for n in [1000,10000]:
            if n not in poly:continue
            y=mp.log(exact_value(poly[n],n**alpha))
            for M in [0,3,9]:
                x=inverse(y,alpha,M)
                out['inverse_checks'].append({'alpha':alpha,'n':n,'M':M,'inverse_minus_n':mp.nstr(x-n,20)})
    with open(args.output,'w') as f:json.dump(out,f,indent=2)
    print(json.dumps({'output':args.output,'rows':len(rows),'last_rows':rows[-4:],'inverse_checks':out['inverse_checks']},indent=2))
if __name__=='__main__':main()
