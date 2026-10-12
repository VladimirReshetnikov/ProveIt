#!/usr/bin/env python3
"""Reproducible checks for Order Derivatives Recover Hidden Polylogarithmic Transseries.

Exact identities and floating-point diagnostics are reported separately.
The latter are not interval certificates or substitutes for the manuscript proofs.
Run from any directory: python verification/verify.py --mode all
Dependencies: mpmath and sympy. Output is written only to --output.
"""
from __future__ import annotations
import argparse
import json
import platform
from pathlib import Path
from typing import Any
import mpmath as mp
import sympy as sp


def exact_checks() -> dict[str, Any]:
    counts: dict[str, int] = {}
    def check(value: bool, category: str) -> None:
        if not value:
            raise AssertionError(category)
        counts[category] = counts.get(category, 0) + 1
    x, u, L, A, xi = sp.symbols('x u L A xi', nonzero=True)
    for m in range(1, 9):
        eps = (-1)**(m+1)
        for j in range(1, 9):
            k = m+2*j-1
            b = sp.bernoulli(k+1, x)
            reflected = b+eps*sp.bernoulli(k+1,1-x)
            check(sp.expand(reflected)==0, 'reflection_tail_cancellation')
            k = m+2*j
            Z = -(sp.bernoulli(k+1,x)+eps*sp.bernoulli(k+1,1-x))/(k+1)
            # Normalize both sides by zeta(2j+1)/(2*pi)^(2j).
            lhs = (-1)**k/sp.factorial(k)*Z*(-1)**j*sp.factorial(2*j)/2
            rhs = (-1)**(m+j+1)*sp.bernoulli(m+2*j+1,x)*sp.factorial(2*j)/sp.factorial(m+2*j+1)
            check(sp.expand(lhs-rhs)==0, 'activated_tail_coefficients')
    simple = xi/(A*A-xi*xi)
    double = 2*A*A*xi/(A*A-xi*xi)**2
    check(sp.simplify(sp.diff(xi*xi/(A*A-xi*xi),xi)-double)==0,'rational_kernels')
    for sign in (-1,1):
        check(sp.residue(simple,xi,sign*A)==-sp.Rational(1,2),'simple_pole_residues')
        check(sp.residue(double,xi,sign*A)==0,'zero_simple_residue_of_double_kernel')
        check(sp.simplify(sp.limit((xi-sign*A)**2*double,xi,sign*A)-sign*A/2)==0,'double_pole_coefficients')
    for m in range(1,25):
        C=(-1)**m/(2*sp.pi*sp.I)**(m+1)
        c=(sp.I/(2*sp.pi))**(m-1)
        check(sp.simplify(4*sp.pi**2*C-c)==0,'normalization_transport')
        check(sp.simplify(4*sp.pi**3*sp.I*C/c-sp.pi*sp.I)==0,'activation_jump_factor')
    # Generic Laurent-residue identities at every jet order tested.
    aa=sp.symbols('a0:10')
    gamma=sp.symbols('g0:9')
    for r in range(7):
        B=sum(aa[k]*u**k for k in range(r+2))
        exponential=sum((-L*u)**k/sp.factorial(k) for k in range(r+2))
        zjet=(-1)**r*sp.factorial(r)/u**(r+1)+(-1)**r*gamma[r]
        raw=sp.expand(B/u*exponential*zjet).coeff(u,-1)
        target=(-1)**r*(sp.factorial(r)*sp.expand(B*exponential).coeff(u,r+1)+gamma[r]*aa[0])
        check(sp.expand(raw-target)==0,'general_collision_jet')
        reflected=sp.expand(raw.subs(aa[0],0))
        check(not reflected.has(gamma[r]),'stieltjes_annihilation')
        check(sp.Poly(reflected,L).degree()==r,'reflection_log_degree')
    # Exact Fourier/Mobius computations in cyclotomic number fields.
    for q in range(3,11):
        cyclo=sp.Poly(sp.cyclotomic_poly(q,x),x,domain=sp.QQ)
        def reduce(p: Any) -> sp.Expr:
            return sp.rem(sp.Poly(p,x,domain=sp.QQ),cyclo).as_expr()
        weights={k:sp.Integer(((7*k+3*q)%9)-4) for k in range(1,q)}
        for m in range(1,5):
            h={n:reduce(sum(c*(x**((k*n)%q)+(-1)**m*x**((-k*n)%q)) for k,c in weights.items())) for n in range(1,2*q+1)}
            D={n:reduce(sum(h[d]/sp.Integer(d)**m for d in sp.divisors(n))) for n in range(1,2*q+1)}
            for n in range(1,2*q+1):
                recovered=reduce(sp.Integer(n)**m*sum(sp.mobius(n//d)*D[d] for d in sp.divisors(n)))
                check(reduce(recovered-h[n])==0,'mobius_reconstruction')
        # The midpoint grid has no Fourier signal before its q-th mode.
        cyc2=sp.Poly(sp.cyclotomic_poly(2*q,x),x,domain=sp.QQ)
        for n in range(1,q+1):
            v=sp.rem(sp.Poly(sum(x**(((2*k+1)*n)%(2*q)) for k in range(q)),x),cyc2).as_expr()
            check(v==(0 if n<q else -q),'sharp_midpoint_delay')
    for r in range(1,7):
        for k in range(1,11):
            lhs=sum(sp.bernoulli(k,(x+j)/r) for j in range(r))
            check(sp.expand(lhs-sp.Rational(1,r)**(k-1)*sp.bernoulli(k,x))==0,'bernoulli_multiplication')
    return {'status':'pass','assertions':sum(counts.values()),'categories':counts}


def zeta_jet(s: int, a: Any, r: int=1) -> Any:
    return mp.diff(lambda v:mp.zeta(v,a),s,r)


def Z(m: int,w: int,a: Any,r: int=0) -> Any:
    eps=(-1)**(m+1)
    return (zeta_jet(w,a,r)+eps*zeta_jet(w,1-a,r)) if r else (mp.zeta(w,a)+eps*mp.zeta(w,1-a))


def original(m: int,t: Any,a: Any,jet: bool=False) -> Any:
    """Absolutely convergent k-series; jet uses -log(k), not finite differences."""
    if not (m>=1 and t>0 and 0<a<1):
        raise ValueError('Require m >= 1, t > 0, and 0 < a < 1.')
    eps=(-1)**(m+1)
    cutoff=int(mp.ceil((mp.mp.dps+12)*mp.log(10)/(min(a,1-a)*t)))
    return mp.fsum((mp.exp(-a*k*t)+eps*mp.exp(-(1-a)*k*t))/(mp.mpf(k)**m*(-mp.expm1(-k*t)))*(-mp.log(k) if jet else 1) for k in range(1,cutoff+1))


def finite_part(m: int,t: Any,a: Any,jet: bool=False) -> Any:
    """P_m or P_m^[1], including the collision residue exactly as stated."""
    n=m-1; eps=(-1)**(m+1)
    ans=(1+eps)*(mp.diff(mp.zeta,m+1) if jet else mp.zeta(m+1))/t
    for k in range(m+1):
        if k==n: continue
        ans+=(-t)**k/mp.factorial(k)*Z(m,-k,a)*(mp.diff(mp.zeta,m-k) if jet else mp.zeta(m-k))
    first=Z(m,-n,a,1)
    if jet:
        ans+=(-t)**n/mp.factorial(n)*((mp.log(t)-mp.harmonic(n)+mp.euler)*first-Z(m,-n,a,2)/2)
    else:
        ans+=(-t)**n/mp.factorial(n)*first
    return ans


def dual_flat(m: int,t: Any,a: Any,jet: bool=False) -> Any:
    eps=(-1)**(m+1); X=4*mp.pi**2/t
    cutoff=int(mp.ceil((mp.mp.dps+12)*mp.log(10)/X))
    def term(k: int) -> Any:
        phase=mp.exp(2j*mp.pi*k*a)+eps*mp.exp(-2j*mp.pi*k*a)
        return phase/mp.mpf(k)**m/mp.expm1(k*X)*(mp.log(t/(2*mp.pi*k)) if jet else 1)
    return (1j*t/(2*mp.pi))**(m-1)*mp.fsum(term(k) for k in range(1,cutoff+1))


def jet_coefficient(m: int,j: int,a: Any) -> Any:
    return (-1)**(m+j+1)*mp.bernpoly(m+2*j+1,a)*mp.factorial(2*j)*mp.zeta(2*j+1)/(mp.factorial(m+2*j+1)*(2*mp.pi)**(2*j))


def I_kernel(lam: Any) -> Any:
    """Simple-pole PV kernel after integration by parts, not a double-pole PV."""
    return -1/lam+(mp.exp(-lam)*mp.ei(lam)+mp.exp(lam)*mp.e1(lam))/2


def median_jet(m: int,t: Any,a: Any,J: int=12,N: int=72) -> Any:
    """Accelerated evaluation of t^m times the linear median of J_m.

    Subtract J asymptotic terms from each I-kernel and sum them globally
    by their exact Bernoulli/zeta coefficients. The remaining N-sum is a
    floating-point truncation, not an interval-certified evaluation.
    """
    eps=(-1)**(m+1); E=[mp.mpc(0) for _ in range(N+1)]
    for d in range(1,N+1):
        val=(mp.exp(2j*mp.pi*d*a)+eps*mp.exp(-2j*mp.pi*d*a))/mp.mpf(d)**m
        for n in range(d,N+1,d):E[n]+=val
    polynomial=t**m*mp.fsum(jet_coefficient(m,j,a)*t**(2*j) for j in range(1,J+1))
    rest=[]
    for n in range(1,N+1):
        lam=4*mp.pi**2*n/t
        subtraction=mp.fsum(mp.factorial(2*j)/lam**(2*j+1) for j in range(1,J+1))
        rest.append(E[n]*(I_kernel(lam)-subtraction))
    return polynomial+(1j*t/(2*mp.pi))**(m-1)*mp.fsum(rest)


def numerical_checks() -> dict[str, Any]:
    mp.mp.dps=90
    rows=[]
    def check(name: str, lhs: Any, rhs: Any, tol: str, parameters: dict[str,Any]) -> None:
        err=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))
        if err>=mp.mpf(tol):
            raise AssertionError(f'{name}: {mp.nstr(err,12)} >= {tol}; {parameters}')
        rows.append({'test':name,'parameters':parameters,'scaled_absolute_error':mp.nstr(err,12),'threshold':tol})
    params=[mp.mpf(1)/3,mp.mpf(1)/2,mp.sqrt(2)/3]
    for m in range(1,7):
        for a in params:
            for t in (mp.mpf(2),mp.mpf(5)):
                check('exact_reflection_completion',original(m,t,a),finite_part(m,t,a)+dual_flat(m,t,a),'1e-75',{'m':m,'t':str(t),'a':mp.nstr(a,18)})
    for m in range(1,6):
        for a in (mp.mpf(1)/3,mp.sqrt(2)/3):
            t=mp.mpf(3+m/2)
            med=median_jet(m,t,a)
            check('exact_order_jet_completion',original(m,t,a,True),finite_part(m,t,a,True)+med+dual_flat(m,t,a,True),'1e-38',{'m':m,'t':str(t),'a':mp.nstr(a,18),'J':12,'N':72})
            med2=median_jet(m,t,a,J=13,N=80)
            check('acceleration_refinement',med,med2,'1e-38',{'m':m,'t':str(t),'a':mp.nstr(a,18)})
    # Independent contour test of the Stokes sign and double-pole multiplier.
    with mp.workdps(55):
        theta=mp.mpf('0.32')
        for lam in (mp.mpf(4),mp.mpf(9)):
            def integral(sign: int) -> Any:
                ray=mp.exp(sign*1j*theta)
                def integrand(x: Any) -> Any:
                    z=x*ray
                    return mp.exp(-lam*z)*2*z/(1-z*z)**2*ray
                return mp.quad(integrand,[0,mp.mpf('0.5'),1,2,4,mp.inf])
            plus,minus=integral(1),integral(-1)
            check('independent_lateral_double_pole_jump',plus-minus,mp.pi*1j*lam*mp.exp(-lam),'1e-42',{'lambda':str(lam)})
            check('independent_linear_median_kernel',(plus+minus)/2,lam*I_kernel(lam),'1e-42',{'lambda':str(lam)})
    # An exponentially small remainder that a power-series-only test misses.
    m=1;t=mp.mpf(2);a=mp.mpf(1)/2
    hidden=original(m,t,a)-finite_part(m,t,a)
    check('nonzero_hidden_remainder',hidden,dual_flat(m,t,a),'1e-75',{'m':m,'t':str(t),'a':'1/2','remainder':mp.nstr(hidden,30)})
    if abs(hidden)<=mp.mpf('1e-12'):
        raise AssertionError('Unexpected hidden-remainder scale.')
    return {'status':'pass','precision_decimal_digits':90,'assertions':len(rows),'checks':rows,'scope':'Non-interval floating-point diagnostics. Infinite identities are proved in the article.'}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode',choices=['all','exact','numerical'],default='all')
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('results.json'))
    args=parser.parse_args()
    report={'python':platform.python_version(),'sympy':sp.__version__,'mpmath':mp.__version__}
    if args.mode in ('all','exact'):report['exact']=exact_checks()
    if args.mode in ('all','numerical'):report['numerical']=numerical_checks()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:({'status':v['status'],'assertions':v['assertions']} if isinstance(v,dict) and 'assertions' in v else v) for k,v in report.items()},indent=2))
if __name__=='__main__':main()
