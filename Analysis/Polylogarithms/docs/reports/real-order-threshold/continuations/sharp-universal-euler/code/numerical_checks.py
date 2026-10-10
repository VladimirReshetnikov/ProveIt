#!/usr/bin/env python3
"""Independent numerical diagnostics. These outputs are NOT interval proofs."""
from __future__ import annotations
from pathlib import Path
from math import comb
import json
import mpmath as mp
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=100

def euler_values(a,b,length):
    H=mp.mpf('0');A=[]
    for k in range(length):
        if k:H+=mp.power(2*k-1,-b)+mp.power(2*k,-b)
        A.append(H/mp.power(2*k+1,a))
    # Triangular differences are only used in high-precision diagnostics.
    row=A;es=[mp.mpf('0')]
    for j in range(length):
        es.append(es[-1]+row[0]/mp.power(2,j+1))
        row=[row[k]-row[k+1] for k in range(len(row)-1)]
    return es

C=lambda b:mp.dirichlet(b,[0,1,0,-1])+mp.power(2,-b)*mp.altzeta(b)
bstar=mp.findroot(lambda b:mp.diff(C,b),(mp.mpf('1.2'),mp.mpf('1.4')))
report={'status':'NONRIGOROUS numerical cross-checks; see exact certificates for proofs',
        'working_dps':mp.mp.dps,'b_star':mp.nstr(bstar,85),'C_star':mp.nstr(C(bstar),85),
        'C_second_derivative_at_maximum':mp.nstr(mp.diff(C,bstar,2),70)}
# Independent elementary F_11 compares with finite Euler sums and all moments.
a=b=mp.mpf(1);length=240
E=euler_values(a,b,length);g=-mp.pi*mp.log(2)/8
f=lambda z:mp.log(1-z)**2/2
D=[lambda z:f(z)]
# Derivatives g_{1-j,1} via radial differentiation of an elementary expression.
gshift=[mp.im(mp.diff(lambda u:f(1j*mp.exp(u)),0,j)) for j in range(7)]
P=[[mp.mpf(1)],[mp.mpf(0),mp.mpf(1)]]
for n in range(1,6):
    out=[mp.mpf(0)]*(n+2)
    for j,c in enumerate(P[n]):out[j+1]+=c/(n+1)
    for j,c in enumerate(P[n-1]):out[j]+=n*c/(n+1)
    P.append(out)
moments=[]
for k in range(6):
    lhs=mp.fsum(mp.mpf(comb(n-1,k))*(E[n]-g) for n in range(k+1,length+1))
    rhs=-mp.fsum(c*gshift[j] for j,c in enumerate(P[k+1]))
    moments.append({'k':k,'lhs':mp.nstr(lhs,65),'rhs':mp.nstr(rhs,65),
                    'absolute_residual':mp.nstr(abs(lhs-rhs),8)})
report['elementary_moment_checks']=moments
report['elementary_g_Euler_error']=mp.nstr(abs(E[-1]-g),8)
# Check generating identity at three q values, including beyond q=1.
generating=[]
for q in [mp.mpf('0.3'),mp.mpf('0.8'),mp.mpf('1.2')]:
    r=mp.sqrt(q/(2-q));gr=mp.im(f(1j*r))
    lhs=mp.fsum((E[n]-g)*q**(n-1) for n in range(1,length+1))
    rhs=(gr/mp.sqrt(q*(2-q))-g)/(1-q)
    generating.append({'q':str(q),'absolute_residual':mp.nstr(abs(lhs-rhs),10)})
report['generating_identity_checks']=generating
# A non-elementary depth-two value from independent path quadrature.
F12=mp.quad(lambda t:1j*mp.polylog(2,1j*t)/(1-1j*t),[0,mp.mpf('.5'),1])
E12=euler_values(mp.mpf(1),mp.mpf(2),200)
report['F12_path_quadrature_g']=mp.nstr(mp.im(F12),75)
report['F12_Euler_vs_path_residual']=mp.nstr(abs(E12[-1]-mp.im(F12)),10)
for aa,bb in [('0.001','1.3'),('0.1','0.1'),('4','1')]:
    es=euler_values(mp.mpf(aa),mp.mpf(bb),200)
    report[f'g_{aa}_{bb}']=mp.nstr(es[-1],65)
# Bounded numerical optimization, intentionally kept separate from proofs.
try:
    from scipy.optimize import differential_evolution
    import math
    maxima=[]
    for n in [1,2,3,4,8,16,32,128]:
        def neg(v):
            p,y=v
            if y>1-1e-7:
                return -2*p*(1-p)**(n-1)*((n+1)+(n-1)*p)/(1+p)**2
            return -((1-p*y*y)**n/(1+p*y*y)-(1-p)**n/(1+p))/(1-y)
        res=differential_evolution(neg,[(0,1),(0,1)],seed=431,tol=1e-10)
        maxima.append({'N':n,'p':float(res.x[0]),'y':float(res.x[1]),'found_maximum':float(-res.fun)})
    def neg_limit(v):
        c,y=v
        return -(math.exp(-c*y*y)-math.exp(-c))/(1-y)
    res=differential_evolution(neg_limit,[(0,40),(0,.999999)],seed=431,tol=1e-11)
    report['kernel_maximum_diagnostics']=maxima
    report['limit_kernel_diagnostic']={'c':float(res.x[0]),'y':float(res.x[1]),'found_maximum':float(-res.fun)}
except ImportError:
    report['kernel_maximum_diagnostics']='SciPy unavailable: optional optimizer skipped'
(ROOT/'data/numerical_diagnostics.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
