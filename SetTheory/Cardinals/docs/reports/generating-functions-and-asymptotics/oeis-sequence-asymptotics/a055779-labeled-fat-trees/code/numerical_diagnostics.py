#!/usr/bin/env python3
"""Non-rigorous 100-digit numerical diagnostics; no interval certification.

Adapted from the prior audit diagnostics, using its exact coefficient engine.
These are approximate evaluations, not rigorous interval enclosures or proofs.
"""
import sys
sys.dont_write_bytecode = True
import json
from math import comb
from fractions import Fraction
import mpmath as mp
from exact_checks import correction_coefficients

if mp.__version__ != '1.3.0':
    raise RuntimeError('Use pinned mpmath 1.3.0 for this reproducibility fixture')
mp.mp.dps=100
def decimal(v):
    return mp.mpf(v.numerator)/v.denominator if isinstance(v,Fraction) else mp.mpf(v)
def fmt(v):
    return mp.nstr(v,35)
def params(M):
    # Well-bracketed scalar equation, using a dimensionless variable s=M*r.
    M=mp.mpf(M)
    sr=mp.findroot(lambda s:s*(1+s/M)*mp.exp(s/M)-1,(mp.mpf('0.1'),mp.mpf('1')))
    r=sr/M
    b=(1+3*r+r*r)/(1+r)
    H=mp.log1p(r)+r*r/(1+r)
    a=mp.log(M)+H
    c=-mp.log(M)-mp.log(b)/2
    # Rational 100-decimal approximation: accurate for fixed finite diagnostics.
    cs=[decimal(x) for x in correction_coefficients(Fraction(str(r)),4)]
    ds=[None,cs[1],cs[2]-cs[1]**2/2,cs[3]-cs[1]*cs[2]+cs[1]**3/3]
    return r,b,H,a,c,cs,ds
def normalized_weights(n,M):
    M=mp.mpf(M)
    return [mp.mpf(comb(n,d))*(1-mp.mpf(d)/n)**d/M**d for d in range(n)]
def logA(n,M):
    return (n-2)*mp.log(n)+(n-1)*mp.log(M)+mp.log(mp.fsum(normalized_weights(n,M)))

asym=[]
for kind in ['fixed_1','fixed_2','fixed_10','moving_n','moving_n_squared','fixed_10^12']:
    for n in [20,80,320,640]:
        M={'fixed_1':1,'fixed_2':2,'fixed_10':10,'moving_n':n,
           'moving_n_squared':n*n,'fixed_10^12':10**12}[kind]
        r,b,H,a,c,cs,ds=params(M)
        ratio=mp.fsum(normalized_weights(n,M))*mp.sqrt(b)*mp.exp(-n*H)
        residuals=[(ratio-mp.fsum(cs[j]/mp.mpf(n)**j for j in range(J+1)))*n**(J+1)
                   for J in range(4)]
        asym.append({'kind':kind,'n':n,'M':M,'r':fmt(r),'normalized_ratio':fmt(ratio),
                     'scaled_remainders_J0_to_J3':[fmt(x) for x in residuals],
                     'next_coefficients_c1_to_c4':[fmt(x) for x in cs[1:5]]})

inverse=[]
for M in [1,2,10]:
    r,b,H,a,c,cs,ds=params(M)
    for n in [20,80,320,640]:
        Y=logA(n,M)
        w=mp.lambertw(mp.exp(a)*Y)
        t=Y/w
        L=w+1
        p0=(2*mp.log(t)-c)/L
        p1=-(p0*p0/2-2*p0+ds[1])/L
        p2=-((p0-2)*p1-p0**3/6+p0*p0-ds[1]*p0+ds[2])/L
        centers=[t+p0,t+p0+p1/t,t+p0+p1/t+p2/t**2]
        inverse.append({'M':M,'threshold_n':n,'log_y':fmt(Y),'t':fmt(t),
                        'centers_J0_to_J2':[fmt(v) for v in centers],
                        'scaled_errors_(Xj-n)*t^(j+1)*L':[fmt((v-n)*t**(j+1)*L) for j,v in enumerate(centers)]})

poisson=[]
for lam in [mp.mpf('0.1'),mp.mpf(1),mp.mpf(4)]:
    for n in [20,80,320,640]:
        weights=normalized_weights(n,mp.mpf(n)/lam)
        R=mp.fsum(weights)
        q=[mp.exp(-lam)*lam**d/mp.factorial(d) for d in range(n)]
        # Includes the Poisson mass beyond the support of the deficit law.
        tv=(mp.fsum(abs(weights[d]/R-q[d]) for d in range(n))+1-mp.fsum(q))/2
        expansion=1-(3*lam**2/2+lam)/n+(9*lam**4/8+16*lam**3/3+4*lam**2)/n**2
        poisson.append({'lambda':fmt(lam),'n':n,'tv':fmt(tv),
                        'proved_bound':fmt(min(1,(3*lam**2+2*lam)/(2*n))),
                        'P6_residual_scaled_n3':fmt((mp.exp(-lam)*R-expansion)*n**3)})

print(json.dumps({'status':'DIAGNOSTICS ONLY','interval_certificate':False,
                  'implementation_origin':'adapted prior independent audit','mpmath_version':mp.__version__,
                  'decimal_precision':mp.mp.dps,'asymptotics':asym,
                  'inverse_at_exact_sequence_thresholds':inverse,'poisson':poisson},sort_keys=True,indent=2))
