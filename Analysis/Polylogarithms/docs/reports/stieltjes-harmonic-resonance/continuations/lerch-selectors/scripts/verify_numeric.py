#!/usr/bin/env python3
"""Independent high-precision diagnostics. These are not interval certificates.

The direct transform uses a convergent z-series and explicitly integrated
monomials, rather than the endpoint/polylogarithm reduction under test.
Euler/Gamma identities additionally use direct quadrature.
"""
from __future__ import annotations
import json, time
from collections import Counter
from pathlib import Path
import mpmath as mp
import sympy as sp
from selector_algebra import (u,s,frobenius_euler,resonance_polynomial)
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=75
results=[]

def val(x):
    if isinstance(x,sp.Basic):
        return mp.mpc(str(sp.N(sp.re(x),85)),str(sp.N(sp.im(x),85)))
    return mp.mpmathify(x)

def poly_coeffs(p):
    return [val(sp.expand(p).coeff(u,j)) for j in range(int(sp.degree(p,u))+1)]

def primitive_power(beta, x0, x1):
    # Integral of x^(beta-1) without division by a zero resonant exponent.
    if abs(beta)<mp.mpf('1e-65'):
        return mp.log(x1/x0)
    return x0**beta*mp.expm1(beta*mp.log(x1/x0))/beta

def direct_transform(p,z,ss,a=1,L=1,N=420):
    coeff=poly_coeffs(p); z=val(z); ss=val(ss); a=val(a); L=val(L)
    def one(n):
        b=a+n
        return mp.fsum(coeff[j]*mp.fsum(mp.binomial(j,k)*(-b)**(j-k)*primitive_power(k+1-ss,b,b+L) for k in range(j+1)) for j in range(len(coeff)))
    return mp.fsum(z**n*one(n) for n in range(N))

def endpoint_transform(p,z,ss,a=1,L=1):
    d=int(sp.degree(p,u)); z=val(z); ss=val(ss); a=val(a); L=val(L)
    out=[]
    for j in range(d+1):
        der=sp.diff(p,u,j)
        pL=val(der.subs(u,sp.Rational(str(mp.re(L))))); p0=val(der.subs(u,0))
        f=mp.fprod(ss-k for k in range(1,j+2))
        out.append(-(pL*mp.lerchphi(z,ss-j-1,a+L)-p0*mp.lerchphi(z,ss-j-1,a))/f)
    return mp.fsum(out)

def check(family,lhs,rhs,tol='1e-48',note=''):
    err=abs(lhs-rhs); scale=max(1,abs(lhs),abs(rhs)); scaled=err/scale
    passed=scaled<mp.mpf(tol)
    results.append({'family':family,'passed':bool(passed),'absolute_error':mp.nstr(err,12),'scaled_error':mp.nstr(scaled,12),'tolerance':tol,'note':note})
    print(f'{family}: {mp.nstr(scaled,5)} {"PASS" if passed else "FAIL"}',flush=True)
    if not passed:
        raise AssertionError(f'{family}: {scaled}, lhs={lhs}, rhs={rhs}')

def main():
    # Nonintegral complex-order transforms, including a nonunit interval and shift.
    cases=[(0,sp.Rational(1,3),mp.mpf('2.4'),1,1),
           (1,sp.Rational(-1,2),mp.mpf('1.7'),1,1),
           (3,sp.Rational(1,2),mp.mpc('3.4','.2'),1,1),
           (4,sp.Rational(-1,3),mp.mpf('.7'),1,1),
           (2,sp.Rational(1,3),mp.mpc('2.3','.1'),mp.mpf('1.25'),2)]
    for d,z,ss,a,L in cases:
        p=sp.Integer(L)**d*frobenius_euler(d,z**L).subs(u,u/L)
        lhs=direct_transform(p,z,ss,a,L)
        rhs=endpoint_transform(p,z,ss,a,L)
        check('Direct series / endpoint transform',lhs,rhs,note=f'd={d}, z={z}, a={a}, L={L}, s={ss}')
    # Resonant integer limits compared with the same independently integrated series.
    for d,z,m in [(0,sp.Rational(1,3),1),(1,sp.Rational(-1,2),2),(2,sp.Rational(1,2),1),(3,sp.Rational(-1,3),3),(4,sp.Rational(1,3),5)]:
        p=frobenius_euler(d,z); rr=resonance_polynomial(d,z); zz=val(z)
        den=(-1)**(d+1-m)*mp.factorial(m-1)*mp.factorial(d+1-m)
        rhs=(val(sp.diff(rr,s).subs(s,m))/zz-(1-zz)*mp.factorial(d)/zz**2*mp.diff(lambda v:mp.polylog(v,zz),m-d-1))/den
        lhs=direct_transform(p,z,m)
        check('Removable-integer selector',lhs,rhs,note=f'd={d}, z={z}, m={m}')
    # One spectral derivative: derivative of the direct integral versus numerator compiler.
    d=2; z=sp.Rational(1,3); zz=val(z); p=frobenius_euler(d,z); rr=resonance_polynomial(d,z)
    # m=1, Pi'(1)=2, coefficient E_1 = H_2.
    num1=val(sp.diff(rr,s).subs(s,1))/zz-(1-zz)*mp.factorial(d)/zz**2*mp.diff(lambda v:mp.polylog(v,zz),-2)
    num2=val(sp.diff(rr,s,2).subs(s,1))/zz-(1-zz)*mp.factorial(d)/zz**2*mp.diff(lambda v:mp.polylog(v,zz),-2,2)
    rhs=(num2/2+mp.mpf('1.5')*num1)/2
    # Direct integrand differentiation, evaluated by numerical quadrature of a rapidly convergent series.
    coeff=poly_coeffs(p)
    fn=lambda x:mp.polyval(list(reversed(coeff)),x)*mp.fsum(-zz**n*mp.log(n+1+x)/(n+1+x) for n in range(240))
    lhs=mp.quad(fn,[0,1])
    check('First spectral jet',lhs,rhs)
    # Euler/digamma and Gamma primitives; no infinite alternating sum is used here.
    for r in [1,2,3]:
        d=2*r; p=frobenius_euler(d,sp.Integer(-1)); coeff=poly_coeffs(p)
        rr=resonance_polynomial(d,sp.Integer(-1))
        q=val(-sp.diff(rr,s).subs(s,1)/sp.factorial(d))
        rhs=q+(-1)**(r+1)*(2**(2*r+1)-1)*mp.factorial(2*r)/(2*mp.pi)**(2*r)*mp.zeta(2*r+1)
        phi=lambda x:(mp.digamma((x+2)/2)-mp.digamma((x+1)/2))/2
        lhs=mp.quad(lambda x:mp.polyval(list(reversed(coeff)),x)*phi(x),[0,1])
        check('Euler-weighted digamma / odd zeta',lhs,rhs,note=f'r={r}')
        ep=poly_coeffs(frobenius_euler(d-1,sp.Integer(-1)))
        lg=lambda x:mp.loggamma(1+x/2)-mp.loggamma((1+x)/2)
        lhs=mp.quad(lambda x:mp.polyval(list(reversed(ep)),x)*lg(x),[0,1])
        check('Euler-weighted log-Gamma primitive',lhs,-rhs/(2*r),note=f'r={r}')
    # Additional low-order polygamma evaluations from the one-center formulas.
    values={2:1+mp.mpf(4)/3*mp.log(2)+12*mp.diff(mp.zeta,-1),
            3:mp.log(mp.pi/2)-mp.mpf(1)/2,
            4:mp.mpf(2)/3*mp.log(2)-mp.mpf(1)/2}
    for m,rhs in values.items():
        phi=lambda x:(-1)**m/(mp.mpf(2)**m*mp.factorial(m-1))*(mp.polygamma(m-1,(1+x)/2)-mp.polygamma(m-1,(2+x)/2))
        lhs=mp.quad(lambda x:(x*x-x)*phi(x),[0,1])
        check('Euler quadratic polygamma identities',lhs,rhs,note=f'm={m}')
    # Quartic Bernoulli Stieltjes and trigamma formulas.
    w=lambda x:x*x*(1-x)**2
    z1=mp.diff(mp.zeta,-3); z2=mp.diff(mp.zeta,-3,2)
    lhs=mp.quad(lambda x:-w(x)*mp.digamma(1+x),[0,1])
    check('Quartic zeroth Stieltjes moment',lhs,4*z1-mp.mpf(1)/45)
    lhs=mp.quad(lambda x:w(x)*mp.polygamma(1,1+x),[0,1])
    check('Quartic trigamma moment',lhs,3*mp.zeta(3)/mp.pi**2-mp.mpf(1)/3)
    # Gauss--Legendre quadrature: recompute at two degrees as an extra check.
    def stieltjes_quad(n):
        X,W=mp.gauss_quadrature(n,'legendre')
        return mp.fsum(W[i]*w((X[i]+1)/2)*mp.stieltjes(1,(X[i]+3)/2)/2 for i in range(n))
    lhs=stieltjes_quad(24)
    rhs=-2*z2-mp.mpf(22)/3*z1+mp.mpf(5)/432
    check('Quartic first Stieltjes moment',lhs,rhs,tol='1e-32',note='24-node Gauss-Legendre quadrature')
    # Confluence: use a weight with an exactly elementary Mellin integral in x:
    # integral_1^2 Phi(e^-mu,s,x) dx = selector d=0.
    # At s=1 use the order-derivative formula, not a difference of infinities.
    for mu in [mp.mpf('.4'),mp.mpf('.15')]:
        zz=mp.exp(-mu)
        t=-(1-zz)/zz**2*mp.diff(lambda v:mp.polylog(v,zz),0)
        mass=(mp.exp(2*mu)-mp.exp(mu))/mu
        compensated=t+mass*(mp.log(mu)+mp.euler)
        # Independently integrate the convergent Hurwitz expansion through k=35.
        integrand=lambda x:mp.exp(mu*x)*(-mp.digamma(x)+mp.fsum((-mu)**k/mp.factorial(k)*mp.zeta(1-k,x) for k in range(1,36)))
        rhs=mp.quad(integrand,[1,2])
        check('Compensated Lerch/Hurwitz expansion',compensated,rhs,tol='1e-39' if mu<mp.mpf('.2') else '1e-36',note=f'mu={mu}; 35 Hurwitz terms')
    # A first mixed derivative of the analytic extension at the origin.
    # w=1 on [1,2], h=1,m=0: integral -x psi(x)-zeta(0,x).
    predicted=mp.quad(lambda x:-x*mp.digamma(x)-mp.zeta(0,x),[1,2])
    def analytic_r(mu):
        return mp.quad(lambda x:mp.exp(mu*x)*(-mp.digamma(x)+mp.fsum((-mu)**k/mp.factorial(k)*mp.zeta(1-k,x) for k in range(1,8))),[1,2])
    check('First mixed confluence derivative',mp.diff(analytic_r,0),predicted)
    # Anchored primitive at s=2: ordinary antiderivative with no exceptional denominator.
    zz=mp.mpf('.3'); a0=mp.mpf('1.1'); aa=mp.mpf('1.6')
    def t2(a):
        return mp.fsum(zz**n*(1/(a+n)-1/(a+n+1)) for n in range(240))
    def t1(a):
        return mp.fsum(zz**n*mp.log1p(1/(a+n)) for n in range(240))
    lhs=mp.quad(t2,[a0,aa])
    rhs=-(t1(aa)-t1(a0))
    check('Anchored shift primitive',lhs,rhs,tol='1e-45')
    report={'status':'PASS','working_decimal_digits':mp.mp.dps,'mpmath_version':mp.__version__,'count':len(results),'families':dict(Counter(r['family'] for r in results)),'maximum_scaled_discrepancy':max((r['scaled_error'] for r in results),key=mp.mpf),'checks':results,'scope':'Floating-point diagnostics, not rigorous error enclosures. Direct geometric sums use 420 terms unless stated otherwise; quadrature tolerances vary.'}
    (ROOT/'results/numerical_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='checks'},indent=2),flush=True)
if __name__=='__main__':
    main()
