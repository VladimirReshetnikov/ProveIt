#!/usr/bin/env python3
"""Independent floating-point diagnostics; NOT interval certification or proof."""
from __future__ import annotations
import argparse,json,platform,time,math
from pathlib import Path
import mpmath as mp
import quadratic_spectrum as q


def run(dps=45):
    mp.mp.dps=dps
    rows=[]
    # Intended to be substantially below working precision to allow independent truncations.
    tol=mp.mpf(10)**(-(dps-12))
    def check(name,lhs,rhs,parameters):
        absolute=abs(lhs-rhs);relative=absolute/max(mp.mpf(1),abs(lhs),abs(rhs))
        row={'name':name,'parameters':parameters,'absolute_residual':mp.nstr(absolute,12),
             'scaled_residual':mp.nstr(relative,12),'pass':bool(relative<tol)}
        rows.append(row)
        print(name,parameters,'scaled residual',mp.nstr(relative,5),flush=True)
        assert row['pass'],row
    # Both Stieltjes parity channels, including masses outside the unshifted binomial radius.
    for astr,bstr,order in [('0.31','0.45',3),('0.63','1.2',2),('0.5','0.8',1)]:
        a,b=mp.mpf(astr),mp.mpf(bstr)
        for parity in [1,-1]:
            Bs=q.bessel_jets(order,a,b,parity)
            for m in range(order+1):
                lhs=(-2)**m*(mp.stieltjes(m,a)+parity*mp.stieltjes(m,1-a))
                rhs=Bs[m]-q.counterterm_jet(m,a,b,parity)
                if parity==1:rhs+=q.pole_jet(m,b)
                check('stieltjes_master',lhs,rhs,{'m':m,'a':astr,'b':bstr,'parity':parity})
    # General spectral continuation, including genuinely complex s.
    for a,b,sval in [(mp.mpf('.27'),mp.mpf('.7'),mp.mpf('1.3')),
                     (mp.mpf('.61'),mp.mpf('1.1'),mp.mpc('.83','.22'))]:
        check('poisson_vs_hurwitz_series',q.even_poisson(sval,a,b),
              q.one_sided_binomial(sval,a,b)+q.one_sided_binomial(sval,1-a,b),
              {'a':str(a),'b':str(b),'s':str(sval)})
    # Three representations of all negative-point derivatives.
    for astr,bstr in [('0.37','0.15'),('0.22','0.8')]:
        a,b=mp.mpf(astr),mp.mpf(bstr)
        for m in range(6):
            one=q.negative_derivative_series(m,a,b)
            h=q.negative_hurwitz(m,a,b)
            check('one_sided_hurwitz_factorization',one,h,{'m':m,'a':astr,'b':bstr})
            bilateral=one+q.negative_derivative_series(m,1-a,b)
            check('finite_polylog_negative_jet',bilateral,q.negative_polylog(m,a,b),
                  {'m':m,'a':astr,'b':bstr})
    # Positive integers: independently expanded rational partial fractions vs finite polylogs.
    for astr,bstr in [('0.31','0.6'),('0.7','1.3')]:
        a,b=mp.mpf(astr),mp.mpf(bstr)
        for N in range(1,6):
            check('positive_polygamma_polylog',q.positive_polygamma(N,a,b),q.positive_polylog(N,a,b),
                  {'N':N,'a':astr,'b':bstr})
    # General monomial weights, including nonzero odd-weight anomalies.
    for astr,bstr in [('0.4','0.2'),('0.3','0.9')]:
        a,b=mp.mpf(astr),mp.mpf(bstr)
        for degree in range(8):
            delta=q.monomial_linear_prime(degree,a,b)-q.monomial_quadratic_prime(degree,a,b)
            check('polynomial_anomaly',delta,q.monomial_anomaly(degree,b),
                  {'degree':degree,'a':astr,'b':bstr})
    for astr,bstr in [('0.24','0.4'),('0.63','1.2')]:
        a,b=mp.mpf(astr),mp.mpf(bstr)
        check('gamma_ratio_bessel',mp.loggamma(1-a)-mp.loggamma(a),q.gamma_ratio_bessel(a,b),
              {'a':astr,'b':bstr})
        # Integral evaluated through Gamma data, not its hyperbolic simplification.
        def gamma_R(t):
            return 2*mp.loggamma(a)+2*mp.loggamma(1-a)-2*mp.re(
                mp.loggamma(a+1j*t)+mp.loggamma(1-a+1j*t))
        z0=mp.exp(2j*mp.pi*a);z=mp.exp(-2*mp.pi*b)*z0
        closed=mp.pi*b*b-b*mp.log(4*mp.sin(mp.pi*a)**2)+mp.re(mp.polylog(2,z)-mp.polylog(2,z0))/mp.pi
        check('gamma_mass_integral',mp.quad(gamma_R,[0,b]),closed,{'a':astr,'b':bstr})
    # Parameter primitive derivative, independent Hurwitz derivative evaluation.
    a=mp.mpf('.43')
    for m in range(4):
        f=lambda x:(-1)**(m+1)*mp.zeta(0,x,derivative=m+1)/(m+1)
        check('stieltjes_parameter_primitive',mp.diff(f,a),mp.stieltjes(m,a),{'m':m,'a':str(a)})
    # Exact-order polylog integral form against a distinct Bessel sum at nonintegral epsilon.
    a,b,e=mp.mpf('.34'),mp.mpf('.8'),mp.mpf('.21')
    # Integrate the actual polylogarithm, independently of the Bessel sum.
    z=lambda t:mp.exp(-2*mp.pi*b*mp.cosh(t)+2j*mp.pi*a)
    # The endpoint t=8 already makes the omitted tail far below working precision.
    lhs=4*mp.pi**(mp.mpf('.5')+e)*b**(-e)/mp.gamma(mp.mpf('.5')+e)*mp.quad(
        lambda t:mp.cosh(e*t)*mp.re(mp.polylog(-e,z(t))),[0,1,2,4,8])
    N=q.cutoffs(a,b)[2]
    rhs=4*mp.pi**(mp.mpf('.5')+e)*b**(-e)/mp.gamma(mp.mpf('.5')+e)*mp.fsum(
        n**e*mp.cos(2*mp.pi*n*a)*mp.besselk(e,2*mp.pi*b*n) for n in range(1,N+1))
    check('polylog_integral_even',lhs,rhs,{'epsilon':str(e),'a':str(a),'b':str(b)})
    lhs=4*mp.pi**(1+e)*b**(mp.mpf('.5')-e)/mp.gamma(1+e)*mp.quad(
        lambda t:mp.cosh((e-mp.mpf('.5'))*t)*mp.im(mp.polylog(-e-mp.mpf('.5'),z(t))),[0,1,2,4,8])
    rhs=4*mp.pi**(1+e)*b**(mp.mpf('.5')-e)/mp.gamma(1+e)*mp.fsum(
        n**(e+mp.mpf('.5'))*mp.sin(2*mp.pi*n*a)*mp.besselk(e-mp.mpf('.5'),2*mp.pi*b*n)
        for n in range(1,N+1))
    check('polylog_integral_odd',lhs,rhs,{'epsilon':str(e),'a':str(a),'b':str(b)})
    # Several masses, using a common-scale spectral derivative rather than factorwise differentiation.
    for astr,bs,weights in [('0.3',['0.2','0.5'],[3,2,1]),
                            ('0.41',['0.7','0.7','1.1'],[1,-2,0,1])]:
        a=mp.mpf(astr);masses=[mp.mpf(t) for t in bs]
        f=lambda s:q.multi_quadratic_binomial(s,a,masses,weights)+q.multi_quadratic_binomial(s,1-a,masses,weights)
        lhs=mp.diff(f,0)
        rhs=mp.mpf(0)
        for b in masses:
            for ell in range(len(weights)):
                coefficient=mp.fsum(weights[d]*math.comb(d,ell)*(-b*b)**(d-ell)
                                     for d in range(ell,len(weights)))
                rhs+=coefficient*q.negative_polylog(ell,a,b)
        check('several_masses_finite_reduction',lhs,rhs,{'a':astr,'masses':bs,'weights':weights})
    return {'status':'PASS','kind':'floating-point diagnostics, NOT interval certificates',
        'dps':dps,'scaled_tolerance':str(tol),'checks':len(rows),
        'max_scaled_residual':str(max(mp.mpf(r['scaled_residual']) for r in rows)),
        'python':platform.python_version(),'mpmath':mp.__version__,'results':rows}


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--dps',type=int,default=45);p.add_argument('--output',type=Path)
    args=p.parse_args()
    if args.dps<30:raise SystemExit('Use at least 30 decimal digits.')
    result=run(args.dps);text=json.dumps(result,indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(text+'\n')
    print(text)
