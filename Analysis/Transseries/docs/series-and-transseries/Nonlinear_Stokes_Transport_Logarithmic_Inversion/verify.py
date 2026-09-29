#!/usr/bin/env python3
"""Reproducible checks for Nonlinear Stokes Transport under Logarithmic Inversion.

Exact symbolic identities are checked with SymPy. Numerical experiments use
mpmath at 100 decimal digits; they are checks, not interval certificates.
Run: python verify.py --out results
"""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path
import mpmath as mp
import sympy as sp


def mul(a, b, n):
    return [sum(a[j]*b[k-j] for j in range(k+1)
                if j < len(a) and k-j < len(b)) for k in range(n+1)]


def power(a, k, n):
    r = [1] + [0]*n
    for _ in range(k):
        r = mul(r, a, n)
    return r


def inverse(a, n):
    if a[0] == 0:
        raise ValueError("A unit power series is required")
    r = [sp.Rational(1,a[0]) if isinstance(a[0], int) else 1/a[0]]
    for k in range(1, n+1):
        r.append(-sum(a[j]*r[k-j] for j in range(1, k+1)
                      if j < len(a))/a[0])
    return r


def exp_series(a, n):
    r = [mp.exp(a[0]) if isinstance(a[0], (mp.mpf, mp.mpc)) else sp.exp(a[0])]
    for k in range(1, n+1):
        r.append(sum(j*a[j]*r[k-j] for j in range(1, k+1)
                     if j < len(a))/k)
    return r


def shift(a, k, n):
    return ([0]*k + a)[:n+1] + [0]*max(0, n+1-k-len(a))


def exact_checks():
    # Direct h-coordinate Lagrange coefficients, compared with inverse jets.
    d1, d2, d3, d4, A = sp.symbols('d_1 d_2 d_3 d_4 A', nonzero=True)
    ds = [d1, d2/2, d3/6, d4/24]
    inv = inverse(ds, 3)
    cs = []
    for n in range(1, 5):
        ex = [(-n*A)**k/sp.factorial(k) for k in range(n)]
        cs.append(sp.expand(sp.Rational((-1)**n, n)*mul(ex, power(inv,n,n-1),n-1)[n-1]))
    g1 = 1/d1
    g2 = -d2/d1**3
    g3 = 3*d2**2/d1**5 - d3/d1**4
    g4 = -15*d2**3/d1**7 + 10*d2*d3/d1**6 - d4/d1**5
    expected = [
        -g1,
        (g2-2*A*g1**2)/2,
        -(g3-9*A*g1*g2+9*A*A*g1**3)/6,
        (g4-16*A*g1*g3-12*A*g2*g2+96*A*A*g1*g1*g2-64*A**3*g1**4)/24]
    assert all(sp.simplify(x-y)==0 for x,y in zip(cs,expected))

    # Independent exact substitution in a polynomial forward map.
    nmax=9
    ds2=[sp.Integer(1),sp.Rational(1,3),-sp.Rational(2,5),sp.Rational(1,7)]
    inv2=inverse(ds2,nmax-1)
    h=[sp.Integer(0)]
    for n in range(1,nmax+1):
        ex=[(-n*sp.Rational(3,2))**k/sp.factorial(k) for k in range(n)]
        h.append(sp.cancel(sp.Rational((-1)**n,n)*mul(ex,power(inv2,n,n-1),n-1)[n-1]))
    residual=[sp.Integer(0)]*(nmax+1)
    for k,d in enumerate(ds2,1):
        p=power(h,k,nmax)
        residual=[x+d*y for x,y in zip(residual,p)]
    eh=exp_series([-sp.Rational(3,2)*x for x in h],nmax)
    residual=[x+y for x,y in zip(residual,shift(eh,1,nmax))]
    assert all(sp.cancel(v)==0 for v in residual)

    # Exact core-coordinate inverse coefficients, no logarithms of y.
    a,b=sp.symbols('a b')
    K=6
    r=[sp.Integer(0)]*(K+1)
    for n in range(1,K+1):
        vr=shift(r,1,K)
        logarithm=[sp.Integer(0)]*(K+1)
        for j in range(1,K+1):
            p=power(vr,j,K)
            logarithm=[x+sp.Rational((-1)**(j+1),j)*y for x,y in zip(logarithm,p)]
        invr=inverse([1+vr[0]]+vr[1:],K)
        u=[sp.Integer(0)]*(K+1)
        for j in range(K):
            p=shift(power(invr,j+1,K),j+1,K)
            u=[x+sp.factorial(j)*y for x,y in zip(u,p)]
        r[n]=sp.expand(-a*logarithm[n]-b*u[n])
    assert r[1] == -b
    assert sp.expand(r[2]-(a*b-b))==0
    assert sp.expand(r[3]+b*(a*a-a+b+2))==0
    assert sp.expand(r[4]-b*(2*a**3-2*a*a+5*a*b+4*a-6*b-12)/2)==0

    # Curvature correction of the critical value through cubic jet order.
    e=sp.symbols('e')
    k2,k3=sp.symbols('k_2 k_3')
    s=-1+k2*e**2/2-k3*e**3/3
    psi=s+k2*e**2*s**2/2+k3*e**3*s**3/6
    q=sp.series(-sp.exp(s)*psi,e,0,4).removeO()
    expectedq=sp.exp(-1)*(1-k2*e**2/2+k3*e**3/6)
    assert sp.simplify(sp.expand(q-expectedq))==0
    return {"generic_inverse_coefficients_through_order":4,
            "independent_residual_zero_through_order":nmax,
            "core_coefficients":[str(sp.factor(r[n])) for n in range(1,K+1)],
            "core_coefficients_latex":[sp.latex(sp.factor(r[n])) for n in range(1,K+1)],
            "fold_critical_value_expansion":"PASS"}


def U(z):
    return mp.exp(-z)*mp.ei(z)


def forward(z,a,b,sigma=0):
    return z+a*mp.log(z)+b*U(z)+sigma*mp.exp(-z)


def jets(z,a,b,N,sigma=0):
    u=U(z)
    ds=[]
    for k in range(1,N+1):
        uk=(-1)**k*(u-sum(mp.factorial(j)/z**(j+1) for j in range(k)))
        dk=(1 if k==1 else 0)+a*(-1)**(k-1)*mp.factorial(k-1)/z**k+b*uk
        dk+=sigma*(-1)**k*mp.exp(-z)
        ds.append(dk/mp.factorial(k))
    return ds


def sectors(z,a,b,N,sigma0=0,A=1):
    ds=jets(z,a,b,N,sigma0)
    inv=inverse(ds,N-1)
    out=[]
    for n in range(1,N+1):
        ex=[(-n*A)**k/mp.factorial(k) for k in range(n)]
        val=mul(ex,power(inv,n,n-1),n-1)[n-1]
        out.append(mp.mpf((-1)**n)/n*mp.exp(-n*A*z)*val)
    return out


def numeric_checks():
    mp.mp.dps=100
    a=mp.mpf(13)/10; b=mp.mpf(7)/10
    rho=mp.mpf('0.5'); theta=mp.pi/4
    central=[]; direct=[]; fold=[]
    fmt=lambda z: mp.nstr(z,35)
    for gi in (8,12,20):
        g=mp.mpf(gi); x=forward(g,a,b)
        p=mp.j*mp.pi*b
        gp=mp.findroot(lambda z:forward(z,a,b,p)-x,(g,g-p*mp.exp(-g)),tol=mp.mpf('1e-95'))
        gm=mp.conj(gp)
        assert abs(forward(gm,a,b,-p)-x)<mp.mpf('1e-85')
        cs=sectors(g,a,b,8)
        jump=gp-gm; bias=(gp+gm)/2-g
        jlead=2*p*cs[0]; blead=p*p*cs[1]
        seriesp=g+sum(p**n*cs[n-1] for n in range(1,7))
        error=abs(gp-seriesp)
        # Explicit disk bound derived from the rays +/- pi/4.
        clower=1-abs(a)/g-abs(b)/(mp.sin(theta)*(g*mp.cos(theta))**2)
        M2=abs(a)/(g-rho)**2+2*abs(b)/(mp.sin(theta)*(g*mp.cos(theta)-rho)**3)
        R=rho*(clower-rho*M2)
        chi=abs(p)*mp.exp(-(g-rho))/R
        bound=rho*chi**7/(7*(1-chi))
        assert 0<chi<1 and error<bound
        central.append({"g":gi,"x":fmt(x),"jump_leading_ratio":fmt(jump/jlead),
                        "bias_leading_ratio":fmt(bias/blead),
                        "order6_error":fmt(error),"order6_bound":fmt(bound),"chi":fmt(chi)})
        cm=sectors(gm,a,b,6,-p)
        for N in (1,2,3,4,5,6):
            prediction=gm+sum((2*p)**n*cm[n-1] for n in range(1,N+1))
            direct.append({"g":gi,"N":N,"absolute_error":fmt(abs(gp-prediction))})

    for gi in (8,16,32,64):
        g=mp.mpf(gi)
        c=jets(g,a,b,1)[0]
        Fg=forward(g,a,b)
        psi=lambda s:(forward(g+s,a,b)-Fg)/c
        psip=lambda s:jets(g+s,a,b,1)[0]/c
        sc=mp.findroot(lambda s:psi(s)+psip(s),(-mp.mpf('1.05'),-mp.mpf('.95')),
                       tol=mp.mpf('1e-95'))
        qc=-mp.exp(sc)*psi(sc)
        ds=jets(g,a,b,3)
        kappa=2*ds[1]/c; eta=6*ds[2]/c
        qapprox=mp.exp(-1)*(1-kappa/2+eta/6)
        sapprox=-1+kappa/2-eta/3
        fold.append({"g":gi,"s_critical":fmt(sc),"q_critical":fmt(qc),
                     "q_approx":fmt(qapprox),"q_approx_error":fmt(abs(qc-qapprox)),
                     "s_approx_error":fmt(abs(sc-sapprox))})
    return {"decimal_precision":100,"a":"13/10","b":"7/10",
            "central_branch_checks":central,"direct_jump_checks":direct,"fold_checks":fold}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out',type=Path,default=Path('results'))
    args=p.parse_args(); args.out.mkdir(parents=True,exist_ok=True)
    exact=exact_checks(); numerical=numeric_checks()
    data={"status":"PASS","sympy_version":sp.__version__,"mpmath_version":mp.__version__,
          "exact":exact,"numerical":numerical,
          "disclaimer":"Floating-point checks are not interval certificates; proofs are in the article."}
    (args.out/'verification.json').write_text(json.dumps(data,indent=2)+'\n')
    lines=['VERIFICATION: PASS','',json.dumps(exact,indent=2),'',json.dumps(numerical,indent=2)]
    (args.out/'verification.txt').write_text('\n'.join(lines)+'\n')
    print('PASS: generic coefficients 1--4; exact substitution through order 9;')
    print('core coefficients through order 6; fold expansion; 100-digit numerical checks.')
    print('Results:',args.out.resolve())

if __name__=='__main__':
    main()
