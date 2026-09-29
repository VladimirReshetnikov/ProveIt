#!/usr/bin/env python3
"""Reproduce exact and numerical checks for inverse harmonic transseries.

Python >=3.10, SymPy and mpmath. Floating-point checks are not interval proofs.
Run from any directory: python verification/verify.py
"""
from __future__ import annotations
import json
from fractions import Fraction
from pathlib import Path
import mpmath as mp
import sympy as sp

OUT = Path(__file__).resolve().parent

def coeffs_c(n: int) -> list[Fraction]:
    if n < 0:
        raise ValueError('n must be nonnegative')
    ans = [Fraction(0)]
    for k in range(1, n + 1):
        r = -sp.bernoulli(2*k, sp.Rational(1, 2))/(2*k)
        ans.append(Fraction(int(sp.numer(r)), int(sp.denom(r))))
    return ans

def exp_coeffs(c: list[Fraction], N: int, degree: int) -> list[Fraction]:
    e = [Fraction(1)]
    for j in range(1, degree + 1):
        e.append(Fraction(N, j)*sum((r*c[r]*e[j-r] for r in range(1,j+1)), Fraction()))
    return e

def inverse_coefficient(c: list[Fraction], n: int) -> Fraction:
    if n < 1 or n >= len(c):
        raise ValueError('need n >= 1 and c through n')
    N = 2*n-1
    return -exp_coeffs(c, N, n)[n]/N

def mpr(q: Fraction) -> mp.mpf:
    return mp.mpf(q.numerator)/q.denominator

def large_order_R(c: list[Fraction], n: int, K: int) -> mp.mpf:
    if 2*K >= n:
        raise ValueError('use n > 2K')
    E = exp_coeffs(c, 2*n-1, K)
    return mp.fsum([(-1)**k*(2*mp.pi)**(2*k)*mpr(E[k]) /
                    mp.fprod(2*n-r for r in range(1,2*k+1)) for k in range(K+1)])

def symbolic_checks(c: list[Fraction]) -> dict:
    z, f1, f2, f3, rho, lam = sp.symbols('z f1 f2 f3 rho lam', nonzero=True)
    p=1/f1; dp=-f2/f1**3; ddp=(3*f2**2-f1*f3)/f1**5
    A1=-rho*p
    A2=rho*p+rho**2*(dp-2*lam*p**2)/2
    A3=-(rho*p+rho**2*(dp-3*lam*p**2)
          +rho**3*(ddp-9*lam*p*dp+9*lam**2*p**3)/6)
    delta=A1*z+A2*z**2+A3*z**3
    q=z*(1-lam*delta+lam**2*delta**2/2)
    residual=f1*delta+f2*delta**2/2+f3*delta**3/6+rho*(q-q**2+q**3)
    stokes=[sp.simplify(sp.expand(residual).coeff(z,j))==0 for j in range(1,4)]
    # Independent finite substitution in log(w/X)+C(w^-2)=0.
    t=sp.symbols('t')
    h=[None]+[inverse_coefficient(c,n) for n in range(1,7)]
    v=1+sum(sp.Rational(h[n].numerator,h[n].denominator)*t**n for n in range(1,7))
    residual2=sp.log(v)+sum(sp.Rational(c[n].numerator,c[n].denominator)*t**n*v**(-2*n)
                          for n in range(1,7))
    rev=sp.series(residual2,t,0,7).removeO().expand()==0
    assert all(stokes) and rev
    return {'stokes_residual_orders_1_to_3':stokes,
            'inverse_reversion_through_6':rev,
            'inverse_coefficients_1_to_8':[str(inverse_coefficient(c,n)) for n in range(1,9)]}

def run() -> None:
    mp.mp.dps=190
    c=coeffs_c(160)
    results={'precision_decimal_digits':mp.mp.dps,'symbolic':symbolic_checks(c)}
    late=[]
    for n in [20,40,80,160]:
        h=inverse_coefficient(c,n)
        lead=2*(-1)**n*mp.gamma(2*n)/(2*mp.pi)**(2*n)
        ratio=mpr(h)/lead
        late.append({'n':n,'ratio_to_factorial_lead':mp.nstr(ratio,22),
                     'abs_error_R1':mp.nstr(abs(ratio-large_order_R(c,n,1)),12),
                     'abs_error_R3':mp.nstr(abs(ratio-large_order_R(c,n,3)),12),
                     'abs_error_R5':mp.nstr(abs(ratio-large_order_R(c,n,5)),12)})
    results['late_coefficients']=late
    optimal=[]
    for xx in [5,10,20,40]:
        X=mp.mpf(xx); M=int(mp.floor(mp.pi*X)); a=X-1/(12*X)
        cm=[mpr(q) for q in c[:M+2]]
        def P(w):
            return mp.log(w)+mp.fsum(cm[j]/w**(2*j) for j in range(1,M+1))
        target=mp.log(X)
        w=mp.findroot(lambda w:mp.digamma(w+mp.mpf('.5'))-target,(a,X))
        u=mp.findroot(lambda w:P(w)-target,(a,X))
        E=abs(cm[M+1])/a**(2*M+2)
        d=1/(12*X**2)-1/(24*a**2)
        ell=1/(24*X**2)-mp.mpf(7)/(960*X**4)
        assert E<min(d,ell)
        assert (2*M+2)*E/a<1/(X+mp.mpf('.5'))
        err=u-w
        assert (-1)**M*err>0
        assert abs(err)<(X+mp.mpf('.5'))*E
        scale=mp.sqrt(X)*mp.exp(-2*mp.pi*X)
        sigma=M+1-mp.pi*X
        correction=mp.pi/12+(2*sigma**2-3*sigma+mp.mpf(7)/12)/(2*mp.pi)
        optimal.append({'X':xx,'M':M,'sigma':mp.nstr(sigma,12),
                        'absolute_error':mp.nstr(abs(err),14),
                        'certified_formula_bound':mp.nstr((X+mp.mpf('.5'))*E,14),
                        'signed_error_over_scale':mp.nstr((-1)**M*err/scale,16),
                        'first_corrected_prediction':mp.nstr(1+correction/X,16),
                        'difference_times_X_squared':mp.nstr(((-1)**M*err/scale-1-correction/X)*X**2,12)})
    results['near_least_term_inverse']=optimal
    stokes=[]
    lam=2*mp.pi*1j; rho=lam
    for R in [1,2,3]:
        w0=mp.mpc(2,-R)
        def r(w):
            q=mp.exp(-lam*w)
            return rho*q/(1+q)
        def F0(w):
            return mp.digamma(w+mp.mpf('.5'))-r(w)
        L=F0(w0)
        root=mp.findroot(lambda w:mp.digamma(w+mp.mpf('.5'))-L,
                         (w0,w0+mp.mpf('.0001')))
        f1=mp.diff(F0,w0,1); f2=mp.diff(F0,w0,2); f3=mp.diff(F0,w0,3)
        p=1/f1; dp=-f2/f1**3; ddp=(3*f2*f2-f1*f3)/f1**5
        A1=-rho*p
        A2=rho*p+rho**2*(dp-2*lam*p*p)/2
        A3=-(rho*p+rho**2*(dp-3*lam*p*p)
             +rho**3*(ddp-9*lam*p*dp+9*lam**2*p**3)/6)
        q=mp.exp(-lam*w0)
        errors=[abs(root-w0),abs(root-w0-A1*q),
                abs(root-w0-A1*q-A2*q*q),abs(root-w0-A1*q-A2*q*q-A3*q**3)]
        assert all(errors[j+1]<errors[j] for j in range(3))
        stokes.append({'minus_imaginary_part':R,'q_magnitude':mp.nstr(abs(q),12),
                       'errors_through_sectors_0_to_3':[mp.nstr(v,12) for v in errors]})
    results['stokes_numerics']=stokes
    # Check the exact integral representation at sample points.
    integral=[]
    for w in [mp.mpf('0.75'),mp.mpf(2),mp.mpf(5)]:
        val=2*mp.quad(lambda t:t/((w*w+t*t)*(mp.exp(2*mp.pi*t)+1)),[0,1,mp.inf])
        err=abs(val-(mp.digamma(w+mp.mpf('.5'))-mp.log(w)))
        assert err<mp.mpf('1e-170')
        integral.append({'w':str(w),'absolute_error':mp.nstr(err,6)})
    results['fermi_integral_checks']=integral
    (OUT/'results.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__':
    run()
