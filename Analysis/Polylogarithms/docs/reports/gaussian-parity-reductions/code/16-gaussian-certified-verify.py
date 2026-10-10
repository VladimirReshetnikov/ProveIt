#!/usr/bin/env python3
"""Reproduce exact identities, outward-rounded certificates and independent checks.

Run from any working directory. --quick skips the independent quadrature tests.
The certificate path itself uses Python integers, not mpmath.
"""
from __future__ import annotations
import argparse,json,time,platform
from fractions import Fraction
from math import comb
from pathlib import Path
import sympy as s
from certified import Evaluator,shifted_chebyshev
from derive_identities import (main as derive_main,reduced_component,odd_family,
                               expected_six,PI,LOG2,beta,zeta)

def fracstr(x):return f'{x.numerator}/{x.denominator}'

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--quick',action='store_true')
    args=parser.parse_args();start=time.time()
    root=Path(__file__).resolve().parents[1];derive_main()
    counts={};checks=0
    # Enough distinct test points prove each fixed cleared-denominator polynomial
    # identity (degree at most a+b-1), not just isolated evaluations of it.
    for a in range(1,9):
        for b in range(1,9):
            for c in range(1,11):
                for n in range(1,a+b+1):
                    A=sum(Fraction((-1)**(b-r)*comb(a+b-r-1,a-1),c**(a+b-r)*n**r)
                          for r in range(1,b+1))
                    B=sum(Fraction((-1)**b*comb(a+b-r-1,b-1),c**(a+b-r)*(n+c)**r)
                          for r in range(1,a+1))
                    assert A+B==Fraction(1,n**b*(n+c)**a);checks+=1
    counts['partial_fraction_rational_equalities']=checks
    counts['partial_fraction_polynomial_instances']=640
    x=s.symbols('x')
    for n in range(41):
        cs=shifted_chebyshev(n)
        assert s.Poly(sum(c*x**j for j,c in enumerate(cs)),x)==s.Poly(s.chebyshevt(n,2*x-1),x)
        assert sum(abs(c) for c in cs)==s.chebyshevt(n,3)
    counts['chebyshev_polynomial_and_norm_checks']=82
    ev=Evaluator(target_digits=35,max_order=12)
    certificates=[]
    # 66 parity-component checks through weight 12; this is broader than the
    # 5 historical rows and 16 displayed weight-8/10 extensions.
    for w in range(2,13):
        for a in range(1,w):
            b=w-a;val=ev.double(a,b,4,1,0)
            comp=val.im if w%2==0 else val.re
            expr=reduced_component(a,b);res=comp-ev.polynomial(expr)
            assert res.contains_zero(),(a,b,res.decimal(40))
            assert res.width()<Fraction(1,10**35),(a,b,float(res.width()))
            certificates.append({'name':f'parity_{a}_{b}','status':'proved identity; interval is a cross-check',
                'value':comp.record(),'value_display':comp.decimal(38),'residual':res.record(),
                'residual_width':fracstr(res.width())})
    counts['certified_parity_residuals']=66
    for m in range(2,6):
        row,rhs=odd_family(m);w=2*m+1
        lhs=ev.ctx.real(0)
        for a,coef in enumerate(row,1):
            lhs=lhs+ev.double(a,w-a,4,1,0).im*Fraction(int(coef.p),int(coef.q))
        res=lhs-ev.polynomial(rhs)
        assert res.contains_zero() and res.width()<Fraction(1,10**35)
        certificates.append({'name':f'odd_family_weight_{w}','status':'proved identity; interval cross-check',
            'residual':res.record(),'residual_width':fracstr(res.width())})
    counts['certified_odd_family_residuals']=4
    # Resonant products x*y=1, including a=b=1. Stuffle is a separate proof.
    for q,xr,yr in [(3,1,2),(4,1,3)]:
        for a in range(1,4):
            for b in range(1,4):
                lhs=ev.double(a,b,q,xr,yr)+ev.double(b,a,q,yr,xr)
                rhs=ev.singles(q,xr)[a]*ev.singles(q,yr)[b]-ev.singles(q,0)[a+b]
                res=lhs-rhs
                assert res.re.contains_zero() and res.im.contains_zero()
                assert max(res.re.width(),res.im.width())<Fraction(1,10**35)
                certificates.append({'name':f'resonant_stuffle_q{q}_{a}_{b}',
                    'status':'proved identity; interval cross-check','residual':res.record()})
    counts['certified_resonant_stuffle_residuals']=18
    # The S4 manuscript identity is checked, NOT promoted to a theorem.
    gg=lambda a,b:ev.double(a,b,4,1,0).im
    S4=gg(4,1)+ev.double(4,1,4,1,2).im
    rhs=(4*gg(4,1)-3*gg(3,2)-9*gg(2,3))/7+ev.polynomial(PI**5/224-s.Rational(27,224)*beta(2)*zeta(3)-2*beta(4)*LOG2)
    res=S4-rhs
    assert res.contains_zero() and res.width()<Fraction(1,10**35)
    certificates.append({'name':'manuscript_S4_candidate','status':'conjectural; small certified residual is not equality',
                         'value':S4.record(),'value_display':S4.decimal(38),'residual':res.record(),
                         'residual_width':fracstr(res.width())})
    counts['conjectural_residual_checks']=1
    independent=[]
    if not args.quick:
        import mpmath as mp
        mp.mp.dps=55
        cases=[(5,1,4,1,0),(1,5,4,1,0),(3,3,4,1,0),(7,1,4,1,0),
               (1,1,3,1,2),(2,3,3,1,2),(1,1,4,1,3),(3,2,4,1,3)]
        for a,b,q,xr,yr in cases:
            xx=mp.exp(2j*mp.pi*xr/q);yy=mp.exp(2j*mp.pi*yr/q)
            def fun(t):
                if t==0:return mp.mpc(0)
                return (-mp.log(t))**(a-1)*xx*mp.polylog(b,xx*yy*t)/(1-xx*t)/mp.factorial(a-1)
            val=mp.quad(fun,[0,mp.mpf('0.25'),mp.mpf('0.75'),1])
            cert=ev.double(a,b,q,xr,yr)
            for vv,iv in [(mp.re(val),cert.re),(mp.im(val),cert.im)]:
                lo=mp.mpf(iv.lo)/ev.ctx.scale;hi=mp.mpf(iv.hi)/ev.ctx.scale
                # Numerical quadrature itself is not certified; compare midpoint.
                assert abs(vv-(lo+hi)/2)<mp.mpf('1e-36')
            independent.append({'indices':[a,b],'level':q,'arguments':[xr,yr],
                                'value_real':mp.nstr(mp.re(val),45),'value_imag':mp.nstr(mp.im(val),45)})
        counts['independent_high_precision_quadratures']=len(cases)
    summary={'python':platform.python_version(),'symbolic_engine':s.__version__,
        'target_decimal_digits':ev.target_digits,'spectral_terms':ev.K,
        'fixed_point_decimal_digits':ev.ctx.digits,'euler_terms_per_single':ev.euler_terms,
        'spectral_disk_error_bound':fracstr(Fraction(16,3*4**ev.K)),
        'counts':counts,'total_interval_certificates':len(certificates),
        'elapsed_seconds':round(time.time()-start,3),
        'trust_boundary':'Exact integer computations and analytic tail theorems; not proof-assistant verification. Quadrature is a non-rigorous independent diagnostic.'}
    (root/'data/certificates.json').write_text(json.dumps(certificates,indent=2)+'\n')
    (root/'data/independent_quadrature.json').write_text(json.dumps(independent,indent=2)+'\n')
    (root/'data/verification.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Verification requires assertions: do not run Python with -O.')
    main()
