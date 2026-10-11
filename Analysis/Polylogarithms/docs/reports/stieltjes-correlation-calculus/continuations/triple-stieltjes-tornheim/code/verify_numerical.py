#!/usr/bin/env python3
"""Independent quadrature and special-function diagnostics, not interval proofs."""
from __future__ import annotations
import argparse
import json
import platform
from pathlib import Path
from collections import Counter
import mpmath as mp
import sympy as sp
from calculus import (I_closed, rational_stieltjes_difference, cot_coefficients,
    direct_stieltjes0_cot_product,direct_loggamma_cot,loggamma_cot_closed,
    cubic_quarter_integral,direct_hurwitz_cot,six_sector_mellin,K,
    direct_triple_gamma0,ZeroOrderPolylogJet,triple_digamma_mellin)

ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument('--dps',type=int,default=50)
args=parser.parse_args()
if args.dps<35:parser.error('--dps must be at least 35')
mp.mp.dps=args.dps
rows=[]; counts=Counter()

def record(group,label,lhs,rhs,digits=None):
    digits=digits or (mp.mp.dps-10)
    residual=abs(lhs-rhs); scale=max(1,abs(rhs))
    passed=residual<mp.mpf(10)**(-digits)*scale
    rows.append({'group':group,'case':label,'lhs':mp.nstr(lhs,args.dps),
                 'rhs':mp.nstr(rhs,args.dps),'absolute_residual':mp.nstr(residual,8),
                 'relative_threshold_digits':digits,'pass':bool(passed)})
    if not passed:
        raise AssertionError(f'{group} {label}: error {residual}')
    counts[group]+=1
    print(f'PASS {group}: {label}; abs.error={mp.nstr(residual,5)}',flush=True)

record('explicit_cubic','quarter-half PV',cubic_quarter_integral(),
    mp.euler+4*mp.log(2)+3*mp.log(mp.pi)-4*mp.loggamma(mp.mpf(1)/4))
for p,q in [(1,4),(1,3),(1,2),(2,5),(2,3)]:
    d=mp.mpf(p)/q
    record('stieltjes0_cot_quadrature',f'{p}/{q}',direct_stieltjes0_cot_product([d]),I_closed(0,d))
    record('loggamma_cot_quadrature',f'{p}/{q}',direct_loggamma_cot(d),loggamma_cot_closed(d))

for q in range(2,9):
    for p in range(1,q):
        d=mp.mpf(p)/q
        record('rational_gamma_reduction',f'{p}/{q}',
            mp.stieltjes(1,1-d)-mp.stieltjes(1,d),rational_stieltjes_difference(p,q))

for fractions in [[(1,4),(1,2)],[(1,5),(1,3),(3,4)],[(1,7),(2,5),(3,5),(5,6)]]:
    b=[mp.mpf(p)/q for p,q in fractions]
    coeff=cot_coefficients(b)
    record('all_depth_direct_quadrature',str(fractions),direct_stieltjes0_cot_product(b),
           mp.fsum(c*I_closed(0,d) for c,d in zip(coeff,b)),digits=args.dps-12)

for us,p,q in [('0.4',1,3),('0.7',2,5)]:
    u=mp.mpf(us);d=mp.mpf(p)/q
    rhs=mp.pi/mp.sin(mp.pi*u)*mp.zeta(1-u,1-d)-mp.pi*mp.cot(mp.pi*u)*mp.zeta(1-u,d)
    record('hurwitz_cot_generator',f'u={us},d={p}/{q}',direct_hurwitz_cot(u,d),rhs,digits=args.dps-12)

x=sp.symbols('x')
def bernoulli_product_integral(orders,shifts):
    """Exact piecewise-polynomial answer, independent of Fourier or polylogs."""
    points=sorted(set([sp.Rational(0),sp.Rational(1),*shifts]))
    out=0
    for lo,hi in zip(points,points[1:]):
        mid=(lo+hi)/2
        integrand=1
        for r,a in zip(orders,shifts):
            arg=x-a-sp.floor(mid-a)
            integrand *= -sp.bernoulli(r,arg)/sp.factorial(r)
        out+=sp.integrate(sp.expand(integrand),(x,lo,hi))
    return sp.factor(out)

# The most expensive family uses 40 digits by default. It remains an
# independent Mellin-quadrature comparison with an EXACT rational target.
with mp.workdps(max(35,args.dps-10)):
    for orders,ss in [((1,1,1),(sp.Rational(0),sp.Rational(1,5),sp.Rational(2,3))),
                      ((1,2,1),(sp.Rational(0),sp.Rational(1,4),sp.Rational(2,3))),
                      ((2,1,2),(sp.Rational(1,7),sp.Rational(2,5),sp.Rational(4,5)))]:
        target=bernoulli_product_integral(orders,ss)
        shifts=[mp.mpf(str(t.p))/int(t.q) for t in ss]
        lhs=six_sector_mellin(orders,shifts)/(2*mp.pi)**sum(orders)
        rhs=mp.mpf(str(target.p))/int(target.q)
        record('six_sector_mellin_vs_bernoulli',f'{orders}; shifts={ss}; exact={target}',lhs,rhs,digits=mp.mp.dps-8)

# A genuinely singular triple is checked by two unrelated integral formulas.
# The polylog order derivative is computed by convergent series, not by
# infinitesimal black-box differentiation of polylog.
with mp.workdps(max(35,args.dps-10)):
    jet=ZeroOrderPolylogJet()
    for p,q in [(1,3),(1,4),(2,5),(3,7),(4,7),(7,8)]:
        d=mp.mpf(p)/q
        theta=2*mp.pi*(mp.frac(d+mp.mpf('.5'))-mp.mpf('.5'))
        z=mp.exp(1j*theta)
        exact=mp.fsum(z**r*mp.loggamma(mp.mpf(r)/q) for r in range(1,q+1))-(jet.alpha+mp.log(q))*z/(1-z)
        record('polylog_boundary_jet_vs_gamma',f'{p}/{q}',jet.value(theta,0),exact,digits=mp.mp.dps-8)
    for ss in [[mp.mpf(0),mp.mpf(1)/4,mp.mpf(2)/3],
               [mp.mpf(0),mp.mpf(1)/5,mp.mpf(3)/7],
               [mp.mpf(1)/7,mp.mpf(2)/5,mp.mpf(4)/5]]:
        label=','.join(mp.nstr(t,12) for t in ss)
        record('triple_digamma_independent_integrals',label,
               triple_digamma_mellin(ss,jet),-direct_triple_gamma0(ss),digits=mp.mp.dps-9)

summary={'schema':'triple-stieltjes-numerical-v1','status':'PASS','python':platform.python_version(),
 'mpmath':mp.__version__,'working_dps':args.dps,'counts':dict(counts),'total_comparisons':len(rows),
 'scope':'Floating-point diagnostics; no intervals and no numerical proof. Three triple-digamma cases are checked independently; higher Stieltjes triple jets are proved analytically, not all numerically evaluated.',
 'comparisons':rows}
(ROOT/'results'/'numerical_checks.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='comparisons'},indent=2))
