#!/usr/bin/env python3
"""Critical-line identities: exact coefficients and independent diagnostics.

The Bernoulli coefficient comparisons are symbolic/exact. Quadratures and
finite elementary-series comparisons are numerical diagnostics, not proofs.
"""
from __future__ import annotations
import json
from math import comb
from pathlib import Path
import mpmath as mp
import numpy as np
import sympy as sp
from scipy.special import roots_genlaguerre
from audit import beta_rule, h_np, gaussian_double_quadrature

ROOT=Path(__file__).resolve().parents[1]

def coefficient_checks():
    t=sp.symbols('t')
    hs=sp.series(1/(1-sp.exp(-t))-1/t,t,0,16).removeO().expand()
    rows=[]
    for b in [sp.Rational(1,10),sp.Rational(1,2),sp.Rational(9,10)]:
        coefficients={'0':'1/2'}
        for j in range(1,8):
            k=2*j-1
            coefficient=sp.bernoulli(2*j)*sp.rf(b,k)/(sp.factorial(2*j)*sp.factorial(k))
            independent=hs.coeff(t,k)*sp.rf(b,k)/sp.factorial(k)
            assert sp.simplify(coefficient-independent)==0
            coefficients[str(k)]=str(coefficient)
        rows.append({'b':str(b),'coefficients':coefficients})
    return rows

def elementary_checks():
    rows=[]
    for b in [.1,.5,.9]:
        v,w=beta_rule(1-b,b,192)
        for T in [.2,1.,4.,10.]:
            direct=float(np.dot(w,h_np(T*v)))
            K=2000
            k=np.arange(1,K+1,dtype=float)
            q=T/(2*np.pi*k)
            partial=.5+float(np.sum(np.sin(b*np.arctan(q))/(np.pi*k*(1+q*q)**(b/2))))
            tail=b*T/(2*np.pi**2*K)
            assert partial-1e-10 < direct < partial+tail+1e-10
            rows.append({'b':b,'T':T,'K':K,'quadrature':direct,
                         'partial_sum':partial,'analytic_tail_bound':tail,
                         'status':'Floating-point diagnostic; inequalities not certified here.'})
    return rows

def laplace_checks():
    mp.mp.dps=60
    rows=[]
    nodes,weights=roots_genlaguerre(160,0)
    weights=weights/sum(weights)
    for b in [.1,.5,.9]:
        v,w=beta_rule(1-b,b,160)
        for q in [.5,1.,2.,7.]:
            integral=float(np.dot(weights,np.dot(h_np(nodes[:,None]*v[None,:]/q),w)))/q
            target=float(mp.power(q,mp.mpf(str(b))-1)*mp.zeta(mp.mpf(str(b)),q)+1/(1-mp.mpf(str(b))))
            err=abs(integral-target)
            assert err<1e-9,(b,q,err)
            rows.append({'b':b,'q':q,'absolute_error':err})
    return rows

def critical_grid():
    # Positive double quadrature has no catastrophic Euler cancellation.
    # This table supports a question; it is not an interval certificate.
    values=[]
    for a in [.01,.025,.05,.1,.2,.3,.4,.5,.6,.7,.8,.9,.95,.975,.99]:
        g=gaussian_double_quadrature(a,1-a,192)
        values.append({'a':a,'b':1-a,'g_approx':g,'minus_two_g':-2*g})
    return {'rows':values,'predicted_supremum':float(mp.pi/4+mp.log(2)/2),
            'strictly_decreasing_on_tested_grid':all(values[j]['minus_two_g']>values[j+1]['minus_two_g'] for j in range(len(values)-1)),
            'status':'Numerical evidence only; no global optimization theorem asserted.'}

if __name__=='__main__':
    result={'exact_Bernoulli_coefficients':coefficient_checks(),
            'elementary_series_diagnostics':elementary_checks(),
            'Laplace_identity_diagnostics':laplace_checks(),
            'critical_constant_grid':critical_grid()}
    (ROOT/'data/critical_identities.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'exact_coefficient_checks':21,'elementary_series_diagnostics':12,
                     'Laplace_diagnostics':12,'critical_grid_points':15,
                     'max_Laplace_error':max(r['absolute_error'] for r in result['Laplace_identity_diagnostics']),
                     'critical_grid_decreasing':result['critical_constant_grid']['strictly_decreasing_on_tested_grid']},indent=2))
