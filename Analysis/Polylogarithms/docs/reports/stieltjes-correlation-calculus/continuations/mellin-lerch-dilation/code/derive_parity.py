#!/usr/bin/env python3
"""Exact Gaussian generalized-harmonic parity formula and independent checks."""
from pathlib import Path
import json
import sympy as sp
import mpmath as mp

PI=sp.pi
L2=sp.log(2)

def parity_formula(p,r):
    assert p>=1 and r>=1 and (p+r)%2==0
    k=p-1
    B=lambda n:sp.Symbol('B'+str(n))
    ans=2**r*sp.binomial(p+r-1,r)*B(p+r)
    for j in range(1,r//2+1):
        eta=(1-sp.Rational(2)**(1-2*j))*sp.zeta(2*j)
        ans+=2**(r-2*j+1)*eta*sp.binomial(p+r-2*j-1,r-2*j)*B(p+r-2*j)
    M=0
    for ell in range(k//2+1):
        j=k-2*ell
        sec=abs(sp.euler(2*ell))*PI**(2*ell)/(2**(2*ell)*sp.factorial(2*ell))
        if j==0:
            d=2*L2 if r==1 else (2**r-2)*sp.zeta(r)
        else:
            d=sp.rf(r,j)*(2**(r+j)-1)*sp.zeta(r+j)/(2**j*sp.factorial(j))
        M+=sec*d
    return sp.expand((-1)**(r+1)*(ans-PI*M/2)/2)

def beta(n):
    return (mp.zeta(n,mp.mpf(1)/4)-mp.zeta(n,mp.mpf(3)/4))/mp.mpf(4)**n

def formula_number(p,r):
    f=parity_formula(p,r)
    fun=sp.lambdify(list(sorted(f.free_symbols,key=str)),f,modules='mpmath')
    return fun(*[beta(int(str(t)[1:])) for t in sorted(f.free_symbols,key=str)])

def quadrature(p,r):
    return mp.quad(lambda t:t**(p-1)*mp.exp(-t)*mp.polylog(r,-mp.exp(-2*t))/(1+mp.exp(-2*t)),[0,1,3,10,mp.inf])/mp.factorial(p-1)

def beta_resolvent(v):
    return (mp.digamma((v+3)/4)-mp.digamma((v+1)/4))/4

def A_euler(z,u,N=450):
    row=[(mp.digamma(n+1-u)-mp.digamma(1-u))/(2*n+1-z) for n in range(N)]
    result=mp.mpc(0)
    factor=mp.mpf(1)/2
    while row:
        result+=factor*row[0]
        row=[row[i]-row[i+1] for i in range(len(row)-1)]
        factor/=2
    return result

def shifted_euler(p,r,z,u,N=450):
    """Finite differences of the defining shifted harmonic sums."""
    h=mp.mpc(0)
    row=[]
    for n in range(N):
        if n:
            h+=(n-u)**(-r)
        row.append(h/(2*n+1-z)**p)
    result=mp.mpc(0)
    factor=mp.mpf(1)/2
    while row:
        result+=factor*row[0]
        row=[row[i]-row[i+1] for i in range(len(row)-1)]
        factor/=2
    return result

def bivar_closed(z,u):
    return -mp.pi/(2*mp.cos(mp.pi*z/2))*(mp.digamma(1-u)-mp.digamma((1+z)/2-u))+mp.pi/mp.sin(mp.pi*u)*beta_resolvent(z-2*u)-beta_resolvent(z)/u

if __name__=='__main__':
    mp.mp.dps=60
    out=[]
    for w in range(2,12,2):
        for r in range(1,w):
            p=w-r
            f=parity_formula(p,r)
            q=quadrature(p,r)
            rhs=formula_number(p,r)
            err=abs(q-rhs)
            assert err<mp.mpf('1e-52'),(p,r,err)
            out.append({'p':p,'r':r,'formula':str(f),'latex':sp.latex(f),'quadrature':mp.nstr(q,55),'abs_error':mp.nstr(err,5)})
            print(p,r,sp.sstr(f),'err',mp.nstr(err,3),flush=True)
    with mp.workdps(180):
        biv=[]
        for z,u in [(mp.mpf('0.19'),mp.mpf('0.12')),(mp.mpc('0.12','0.09'),mp.mpc('0.17','-0.04')),(mp.mpf('0.31'),mp.mpf('0.63'))]:
            lhs=A_euler(z,u)+A_euler(-z,-u)
            rhs=bivar_closed(z,u)
            err=abs(lhs-rhs)
            assert err<mp.mpf('1e-115'),err
            biv.append({'z':str(z),'u':str(u),'absolute_error':mp.nstr(err,8),'method':'450 Euler terms, 180 decimal digits'})
        mixed=[]
        for p,r,z,u in [(1,2,mp.mpf('0.21'),mp.mpf('0.13')),(2,1,mp.mpf('0.15'),mp.mpf('0.24')),(2,3,mp.mpf('0.19'),mp.mpf('0.11'))]:
            lhs=shifted_euler(p,r,z,u)+(-1)**(p+r)*shifted_euler(p,r,-z,-u)
            rhs=mp.diff(lambda zz:mp.diff(lambda uu:bivar_closed(zz,uu),u,r-1),z,p-1)/(mp.factorial(p-1)*mp.factorial(r-1))
            err=abs(lhs-rhs)
            assert err<mp.mpf('1e-115'),(p,r,err)
            mixed.append({'p':p,'r':r,'z':str(z),'u':str(u),'absolute_error':mp.nstr(err,8),'method':'450 Euler terms against arbitrary precision derivatives, 180 decimal digits'})
        quarter=shifted_euler(1,1,mp.mpf(0),mp.mpf(1)/4)+shifted_euler(1,1,mp.mpf(0),-mp.mpf(1)/4)
        exact_quarter=mp.pi*(mp.log(1+mp.sqrt(2))-1)
        assert abs(quarter-exact_quarter)<mp.mpf('1e-115')
        quarter_record={'value':mp.nstr(quarter,150),'absolute_error':mp.nstr(abs(quarter-exact_quarter),8)}
    (Path(__file__).resolve().parents[1] / 'results' / 'parity_checks.json').write_text(json.dumps({'scalar_checks':out,'bivariate_checks':biv,'mixed_derivative_checks':mixed,'quarter_shift':quarter_record},indent=2)+'\n')
