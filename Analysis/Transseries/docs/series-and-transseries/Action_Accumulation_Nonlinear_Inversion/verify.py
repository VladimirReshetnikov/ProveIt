#!/usr/bin/env python3
"""Reproducible checks for Action Accumulation and Nonlinear Inversion.

Requires Python >= 3.10, mpmath and sympy. No network access is needed.
Analytic truncation bounds are evaluated with high-precision floating point;
these are consistency checks, NOT outward-rounded interval certificates.
Run: python verify.py --output verification_results.json
"""
from __future__ import annotations
import argparse
import json
import platform
from fractions import Fraction
from pathlib import Path
import mpmath as mp
import sympy as sp


def text(x: object, digits: int = 35) -> str:
    return mp.nstr(x, digits) if isinstance(x, (mp.mpf, mp.mpc)) else str(x)


def a_direct(x: mp.mpf, derivative: int = 0, order: int = 75):
    """Independent finite sum + Hurwitz-zeta tail, with Taylor error bound."""
    if x <= 0 or derivative < 0 or order < 1:
        raise ValueError("Require x>0, derivative>=0, order>=1")
    jmax = max(40, int(mp.ceil(2*x)))
    finite = mp.fsum(mp.exp(-x/j)/mp.mpf(j)**(2+derivative)
                     for j in range(1, jmax+1))
    tail = mp.fsum((-x)**k/mp.factorial(k) * mp.zeta(2+derivative+k, jmax+1)
                   for k in range(order))
    err = x**order/mp.factorial(order)*mp.zeta(2+derivative+order,jmax+1)
    return (-1)**derivative*(finite+tail), err


def e_bessel(x: mp.mpf, modes: int):
    if x <= 0 or modes < 1:
        raise ValueError("Require x>0 and modes>=1")
    return 4*mp.re(mp.fsum(mp.sqrt(2*mp.pi*1j*k/x) *
                           mp.besselk(1,2*mp.sqrt(2*mp.pi*1j*k*x))
                           for k in range(1,modes+1)))


def mode_tail(x: mp.mpf, modes: int):
    """Theorem's first-term-plus-integral bound, valid for x>=1."""
    if x < 1 or modes < 1:
        raise ValueError("Tail bound requires x>=1 and modes>=1")
    c = 2*mp.sqrt(mp.pi*x)
    C = 2*mp.sqrt(mp.pi)*(2*mp.pi)**mp.mpf('.25')*x**mp.mpf('-.75')
    d = 3/(16*mp.sqrt(2*mp.pi*x))
    L = modes+1
    def J(alpha):
        return L**alpha*mp.exp(-c*mp.sqrt(L)) + 2*c**(-2*alpha-2)*mp.gammainc(2*alpha+2,c*mp.sqrt(L),mp.inf)
    return C*(J(mp.mpf('.25'))+d*J(mp.mpf('-.25')))


def convolution(a: dict[Fraction,mp.mpf], b: dict[Fraction,mp.mpf]):
    out: dict[Fraction,mp.mpf] = {}
    for s, v in a.items():
        for t, w in b.items():
            out[s+t] = out.get(s+t,mp.mpf('0'))+v*w
    return out


def finite_inverse_check():
    atoms = {Fraction(1):mp.mpf('.12'), Fraction(3,2):mp.mpf('.07')}
    y = mp.mpf(2); b = mp.mpf('1.5'); N = 7
    def val(s): return mp.mpf(s.numerator)/s.denominator
    def h(x): return mp.fsum(v*mp.exp(-val(s)*x) for s,v in atoms.items())
    powers = {Fraction(0):mp.mpf(1)}
    displacement = mp.mpf(0)
    sectors = []
    for n in range(1,N+1):
        powers = convolution(powers,atoms)
        dn = mp.fsum(val(s)**(n-1)*v*mp.exp(-val(s)*y) for s,v in powers.items())/mp.factorial(n)
        sectors.append(dn); displacement += dn
    root = mp.findroot(lambda x:x+h(x)-y,(y-mp.mpf('.1'),y))
    q = b*h(y)
    assert q < 1/mp.e
    bound = (mp.e*q)**(N+1)/(b*(N+1)*(1-mp.e*q))
    upper = y-displacement
    err = upper-root
    assert 0 < err < bound
    return dict(y=text(y),N=N,q=text(q),root=text(root),upper=text(upper),
                actual_error=text(err),tail_bound=text(bound),
                positive_sectors=[text(v) for v in sectors],passed=True)


def truncated_product(a, b, degree):
    c = [mp.mpf(0)]*(degree+1)
    for i in range(min(len(a),degree+1)):
        for j in range(min(len(b),degree-i+1)):
            c[i+j] += a[i]*b[j]
    return c


def accumulation_inverse_check():
    y=mp.mpf(5); a=mp.mpf(1); kappa=mp.mpf(1); N=6
    av=[a_direct(y,r)[0] for r in range(N)]
    hj=[kappa*mp.exp(-a*y)*mp.fsum(mp.binomial(r,l)*(-a)**(r-l)*av[l]
          for l in range(r+1))/mp.factorial(r) for r in range(N)]
    sectors=[]
    for n in range(1,N+1):
        poly=[mp.mpf(1)]
        for _ in range(n): poly=truncated_product(poly,hj,n-1)
        sectors.append((-1)**(n+1)*poly[n-1]/n)
    def h(x): return kappa*mp.exp(-a*x)*a_direct(x)[0]
    root=mp.findroot(lambda x:x+h(x)-y,(y-mp.mpf('.01'),y),tol=mp.mpf('1e-80'))
    upper=y-mp.fsum(sectors); q=(a+1)*h(y)
    bound=(mp.e*q)**(N+1)/((a+1)*(N+1)*(1-mp.e*q))
    err=upper-root
    assert all(d>0 for d in sectors)
    assert 0<err<bound
    core=mp.findroot(lambda x:x+kappa*mp.exp(-a*x)/x-y,(y-mp.mpf('.01'),y))
    return dict(y=text(y),N=N,q=text(q),root=text(root),upper=text(upper),
                actual_error=text(err),tail_bound=text(bound),core_inverse=text(core),
                inverse_minus_core=text(root-core),positive_sectors=[text(v) for v in sectors],passed=True)


def symbolic_checks():
    a,y=sp.symbols('a y',positive=True)
    rows=[]
    for n in range(1,7):
        direct=sp.diff(sp.exp(-n*a*y)*y**(-n),y,n-1)*(-1)**(n-1)/sp.factorial(n)
        formula=sp.exp(-n*a*y)/sp.factorial(n)*sum(
            sp.binomial(n-1,r)*(n*a)**(n-1-r)*sp.rf(n,r)*y**(-n-r)
            for r in range(n))
        assert sp.simplify(direct-formula)==0
        rows.append(dict(n=n,polynomial=str(sp.expand(formula/sp.exp(-n*a*y)))))
    for n in range(1,13):
        assert sp.rf(n,n-1)/sp.factorial(n)==sp.catalan(n-1)
    b=sp.Integer(1); b_rows=[]
    for m in range(9):
        exact=sp.binomial(sp.Rational(1,2),m)*sp.rf(sp.Rational(3,2),m)/2**m
        assert sp.simplify(b-exact)==0
        b_rows.append(str(b)); b*=sp.Rational(4-(2*m+1)**2,8*(m+1))
    return dict(core_coefficients=rows,bessel_coefficients=b_rows,passed=True)


def poisson_checks():
    rows=[]
    for xi in (10,40,100):
        x=mp.mpf(xi); modes=12
        A, direct_bound=a_direct(x)
        E=A-1/x
        with mp.workdps(65):
            EB=e_bessel(x,modes)
        tail=mode_tail(x,modes); err=abs(E-EB)
        C=2*mp.sqrt(mp.pi)*(2*mp.pi)**mp.mpf('.25')*x**mp.mpf('-.75')
        c=2*mp.sqrt(mp.pi*x)
        assert err < tail+direct_bound
        rows.append(dict(x=xi,modes=modes,E=text(E,55),bessel_sum=text(EB,55),
                         discrepancy=text(err),bessel_tail_bound=text(tail),
                         direct_Taylor_bound=text(direct_bound),
                         normalized_E=text(E/(C*mp.exp(-c))),
                         leading_cosine=text(mp.cos(c-mp.pi/8)),passed=True))
    return rows



def finite_composition_check():
    mu={Fraction(1):mp.mpf('.12'),Fraction(3,2):mp.mpf('.07')}
    eta={Fraction(2,3):mp.mpf('.03'),Fraction(2):mp.mpf('.02')}
    x=mp.mpf(2); K=10
    def v(s): return mp.mpf(s.numerator)/s.denominator
    def lap(atoms,z): return mp.fsum(c*mp.exp(-v(s)*z) for s,c in atoms.items())
    hm=lap(mu,x)
    result=dict(mu); power={Fraction(0):mp.mpf(1)}
    for k in range(K+1):
        weighted={s:c*(-v(s))**k/mp.factorial(k) for s,c in eta.items()}
        for t,c in convolution(weighted,power).items():
            result[t]=result.get(t,mp.mpf(0))+c
        power=convolution(power,mu)
    approx=x+lap(result,x)
    exact=x+hm+lap(eta,x+hm)
    err=abs(approx-exact)
    bound=mp.fsum(abs(c)*mp.exp(-v(t)*x)*mp.exp(v(t)*abs(hm))*
                 (v(t)*abs(hm))**(K+1)/mp.factorial(K+1) for t,c in eta.items())
    assert err<bound
    return dict(x=text(x),K=K,actual_error=text(err),Taylor_tail_bound=text(bound),passed=True)


def zero_bracket_checks():
    """Finite asymptotic formula + analytic remainder; floating-point tests only."""
    N=16; K=8
    coeff=[mp.mpf(1)]
    for m in range(N):
        coeff.append(coeff[-1]*(4-(2*m+1)**2)/(8*(m+1)))
    def h_approx(c):
        # Divide E_{K,N} by its positive first-mode envelope to avoid underflow.
        return mp.fsum(mp.mpf(k)**mp.mpf('.25')*mp.exp(-c*(mp.sqrt(k)-1))*
            mp.fsum(coeff[m]/(mp.sqrt(2)*c*mp.sqrt(k))**m*
                    mp.cos(c*mp.sqrt(k)-mp.pi/8+m*mp.pi/4) for m in range(N))
            for k in range(1,K+1))
    def h_error(c):
        x=c*c/(4*mp.pi)
        C=2*mp.sqrt(mp.pi)*(2*mp.pi)**mp.mpf('.25')*x**mp.mpf('-.75')
        local=abs(coeff[N])/(mp.sqrt(2)*c)**N*mp.fsum(
            mp.mpf(k)**(mp.mpf('.25')-mp.mpf(N)/2)*mp.exp(-c*(mp.sqrt(k)-1))
            for k in range(1,K+1))
        return local+mode_tail(x,K)/(C*mp.exp(-c))
    rows=[]
    for m in (5,10,20):
        c0=(m+mp.mpf(5)/8)*mp.pi
        center=mp.findroot(h_approx,(c0-mp.mpf('.02'),c0))
        radius=mp.mpf('1e-8')
        lo=center-radius; hi=center+radius
        hl=h_approx(lo); hh=h_approx(hi)
        bl=h_error(lo); bh=h_error(hi)
        assert (hl-bl>0 and hh+bh<0) or (hl+bl<0 and hh-bh>0)
        x=center*center/(4*mp.pi)
        predicted=mp.pi/4*(m+mp.mpf(5)/8)**2-3/(32*mp.pi)
        rows.append(dict(m=m,approximate_c=text(center),approximate_x=text(x),
                         c_bracket_radius=text(radius),
                         normalized_analytic_error_bound=text(max(bl,bh)),
                         x_minus_refined_asymptotic=text(x-predicted),passed=True))
    return dict(K=K,N=N,scope='Floating-point evaluations of analytically bounded sign brackets; not rounded interval proofs.',rows=rows)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',default='verification_results.json',type=Path)
    parser.add_argument('--dps',default=120,type=int)
    args=parser.parse_args()
    if args.dps<110:
        parser.error('Use at least 110 digits; cancellation in the independent Hurwitz-zeta evaluation is severe.')
    mp.mp.dps=args.dps
    result={
        'scope':'High-precision consistency tests, not interval arithmetic or formal verification.',
        'environment':{'python':platform.python_version(),'mpmath':mp.__version__,
                       'sympy':sp.__version__,'decimal_precision':mp.mp.dps,'Bessel_decimal_precision':65},
        'symbolic':symbolic_checks(),
        'poisson_bessel':poisson_checks(),
        'finite_atomic_inverse':finite_inverse_check(),
        'finite_composition':finite_composition_check(),
        'zero_brackets':zero_bracket_checks(),
        'accumulating_atomic_inverse':accumulation_inverse_check(),
    }
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
