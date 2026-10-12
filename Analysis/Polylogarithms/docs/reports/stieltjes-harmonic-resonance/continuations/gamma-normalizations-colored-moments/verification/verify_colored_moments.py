#!/usr/bin/env python3
"""Independent exact and numerical checks of the colored moment section.

This script writes evidence into the package evidence directory, requires mpmath and sympy, and
does not use the network. Direct kernel quadratures use the elementary
series inside |omega|<1, not Stieltjes-constant quadrature. Numeric tests
are diagnostics at 50 decimal digits, not rigorous error enclosures.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import mpmath as mp
import sympy as sp


def exact_checks():
    assertions = 0
    ell = sp.symbols('ell')
    # Compare the finite-zeta formula against the independently expanded
    # binomial polynomial in the absolutely convergent positive series.
    for m in range(1, 8):
        poly = sp.Poly(sp.prod(ell-j for j in range(1, m))
                       / sp.factorial(m-1), ell)
        e = [sp.Integer(1)]+[sp.Integer(0)]*(m-1)
        for j in range(1, m):
            for k in range(m-1, 0, -1):
                e[k] += e[k-1]/j
        for q in range(m, m+3):
            positive = {q+1-j: (-1)**q*sp.factorial(q)*poly.nth(j)
                        for j in range(m)}
            finite = {q+1-j: (-1)**(m+q+1+j)*sp.factorial(q)*e[j]
                      for j in range(m)}
            assert positive == finite, (m,q,positive,finite)
            assertions += 1

    w, a, z = sp.symbols('w a z')
    ar = [1/(1-w)]
    for k in range(4):
        ar.append(sp.factor(w*sp.diff(ar[-1],w)+a*ar[-1]))
    a0, w0 = (1+sp.sqrt(2))/2, -3-2*sp.sqrt(2)
    factor = ((3-2*sp.sqrt(2))*(w+3+2*sp.sqrt(2))**2
              /(4*(1-w)**3))
    assert sp.simplify(ar[2].subs(a,a0)-factor) == 0
    vals = [sp.simplify(v.subs({a:a0,w:w0})) for v in ar]
    assert vals[2] == 0
    assert vals[3] == 0
    assert sp.simplify(vals[4]-(2-sp.sqrt(2))/64) == 0
    assert sp.diff(sp.rf(1+z,4),z,2).subs(z,0)/24 == sp.Rational(35,12)
    assert sp.diff(sp.rf(1+z,4),z,3).subs(z,0)/24 == sp.Rational(5,2)
    assert [2*x-y for x,y in zip([1,3,3,1],[1,2,1,0])] == [1,4,5,2]
    assertions += 7

    # Negative odd Lerch orders at the alternating half shift vanish.
    # Build them using the rational order-lowering operator itself.
    f = 1/(1-w)
    zeros = []
    for k in range(1,12):
        f = sp.cancel(w*sp.diff(f,w)+f/2)
        if k % 2:
            value = sp.simplify(f.subs(w,-1))
            assert value == 0
            zeros.append(k)
            assertions += 1

    # The centered and uncentered constant terms can also be checked
    # without Lerch continuation, from the elementary Bernoulli generator.
    lam = sp.symbols('lambda')
    generator = sum(sp.bernoulli(k,1-a)*lam**(k-1)/sp.factorial(k)
                    for k in range(9))
    for m in range(1,8):
        differentiated = sp.expand((-1)**(m-1)*sp.diff(generator,lam,m-1))
        ct = differentiated.coeff(lam,0)
        assert sp.simplify(ct+sp.bernoulli(m,a)/m) == 0
        assertions += 1

    return dict(assertions=assertions,
                finite_zeta_coefficient_identities=21,
                counterexample=dict(a=str(a0),omega=str(w0),
                                    A2=str(vals[2]),A3=str(vals[3]),A4=str(vals[4]),
                                    alternative_coefficients=[1,4,5,2]),
                negative_odd_zero_orders=zeros,
                centered_Bernoulli_constants=7)


def serialize(z, digits=43):
    z=mp.mpc(z)
    if not z.imag:
        return mp.nstr(z.real,digits)
    return dict(real=mp.nstr(z.real,digits),imag=mp.nstr(z.imag,digits))


def record(name, left, right, tolerance=mp.mpf('2e-40'), **parameters):
    residual=abs(left-right)
    assert residual < tolerance, (name,mp.nstr(residual,15),left,right)
    return dict(name=name,parameters=parameters,
                direct=serialize(left),formula=serialize(right),
                absolute_residual=mp.nstr(residual,8),
                tolerance=mp.nstr(tolerance,5))


def elementary_kernel(q, omega, a, nmax=100):
    terms=[]
    power=mp.mpc(1)
    for n in range(nmax):
        terms.append((power,a+n))
        power*=omega
    sign=(-1)**q
    def kernel(x):
        return sign*mp.fsum(power*mp.log1p(c/x)**q/(x+c)
                           for power,c in terms)
    return kernel


def Lmq(m,q):
    e=[mp.mpf(1)]+[mp.mpf(0)]*(m-1)
    for j in range(1,m):
        for k in range(m-1,0,-1):
            e[k]+=e[k-1]/j
    return (-1)**(m+q+1)*mp.factorial(q)*mp.fsum(
        (-1)**j*e[j]*mp.zeta(q+1-j) for j in range(m))


def negative_lerch(n,omega,a):
    # n=0,1 suffice for the direct integer quadratures below.
    if n==0:
        return 1/(1-omega)
    if n==1:
        return a/(1-omega)+omega/(1-omega)**2
    return mp.lerchphi(omega,-n,a)


def Q(q,u):
    return mp.diff(lambda z:mp.gamma(u+z)/(mp.gamma(u)*mp.gamma(1+z)),0,q)


def direct_mellin(q,omega,a,u):
    kernel=elementary_kernel(q,omega,a)
    def f(x):
        if x==0 or not mp.isfinite(x):
            return mp.mpc(0)
        return x**(u-1)*kernel(x)
    return mp.quad(f,[0,1,mp.inf])


def uncolored(q,x,a):
    lx=mp.log(x)
    return lx**(q+1)/(q+1)+mp.fsum(
        (-1)**j*math.comb(q,j)*mp.stieltjes(j,x+a)*lx**(q-j)
        for j in range(q+1))


def numeric_checks():
    mp.mp.dps=50
    results=[]
    for q,m,omega,a in [
        (1,1,mp.mpf('.2'),mp.mpf('.7')),
        (2,2,mp.mpf('.25'),mp.mpf('1.3')),
        (3,2,mp.mpc('.1','.2'),mp.mpf('.9')),
    ]:
        direct=direct_mellin(q,omega,a,m)
        formula=Lmq(m,q)*negative_lerch(m-1,omega,a)
        results.append(record('integer moment from elementary-series quadrature',
                              direct,formula,q=q,m=m,
                              omega=str(omega),a=str(a),series_terms=100))
    for q,u,omega,a in [
        (1,mp.mpc('.7','.3'),mp.mpf('.2'),mp.mpf('.8')),
        (3,mp.mpc('2.2','.1'),mp.mpf('.15'),mp.mpf('1.1')),
    ]:
        direct=direct_mellin(q,omega,a,u)
        formula=mp.pi/mp.sin(mp.pi*u)*Q(q,u)*mp.lerchphi(omega,1-u,a)
        results.append(record('noninteger Mellin moment from elementary-series quadrature',
                              direct,formula,tolerance=mp.mpf('2e-34'),q=q,u=str(u),
                              omega=str(omega),a=str(a),series_terms=100))

    # A Stieltjes dictionary point evaluation is much faster and more
    # independent than quadrature of expensive Stieltjes order derivatives.
    for q,d,x,a in [(1,2,mp.mpf('1.2'),mp.mpf('.7')),
                    (2,3,mp.mpf('.8'),mp.mpf('1.4'))]:
        omega=mp.exp(2j*mp.pi/d)
        dictionary=mp.fsum(omega**r*uncolored(q,x/d,(a+r)/d)
                           for r in range(d))/d
        direct=mp.diff(lambda z:x**z*mp.lerchphi(omega,1+z,x+a),0,q)
        results.append(record('root-of-unity Stieltjes dictionary versus Lerch jet',
                              dictionary,direct,q=q,d=d,x=str(x),a=str(a)))

    # These test the exceptional-moment normalization through independent
    # Hurwitz order derivatives, rather than slow Stieltjes quadrature.
    def alternating_phi(s):
        return 2**(-s)*(mp.zeta(s,mp.mpf('.25'))-mp.zeta(s,mp.mpf('.75')))
    for r in (1,2):
        s0=1-2*r
        derivative=-mp.diff(alternating_phi,s0)
        beta=mp.dirichlet(2*r,[0,1,0,-1])
        formula=(-1)**r*mp.factorial(2*r-1)*beta/mp.pi**(2*r-1)
        results.append(record('exceptional beta moment via Hurwitz order derivative',
                              derivative,formula,r=r,spectral_order=s0))

    q,omega,x,a0,a=1,mp.mpf('.2'),mp.mpf('.8'),mp.mpf('.4'),mp.mpf('1.3')
    primitive_direct=mp.quad(lambda v:elementary_kernel(q,omega,v)(x),[a0,a])
    primitive_formula=-mp.diff(
        lambda z:x**z*(mp.lerchphi(omega,z,x+a)-mp.lerchphi(omega,z,x+a0)),
        0,q+1)/(q+1)
    results.append(record('anchored shift primitive',primitive_direct,primitive_formula,
                          q=q,omega=str(omega),x=str(x),a0=str(a0),a=str(a)))

    m,q,a,lam=2,2,mp.mpf('.7'),mp.mpf('.2')
    omega=mp.exp(-lam)
    direct=mp.exp(-a*lam)*Lmq(m,q)*negative_lerch(m-1,omega,a)
    expansion=Lmq(m,q)*(mp.gamma(m)/lam**m+mp.fsum(
        (-lam)**k/mp.factorial(k)*mp.zeta(1-m-k,a) for k in range(40)))
    results.append(record('convergent centered color-one expansion',direct,expansion,
                          m=m,q=q,a=str(a),lambda_value=str(lam),series_terms=40))
    return results


if __name__=='__main__':
    exact=exact_checks()
    numeric=numeric_checks()
    report=dict(exact=exact,working_precision=50,numerical_checks=len(numeric),
                numerical=numeric,
                numerical_status='Floating-point diagnostics; no certified error bounds claimed.',
                dependencies=dict(mpmath=mp.__version__,sympy=sp.__version__))
    target=(Path(__file__).resolve().parent.parent / 'evidence' / 'colored_moments_validation.json')
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
