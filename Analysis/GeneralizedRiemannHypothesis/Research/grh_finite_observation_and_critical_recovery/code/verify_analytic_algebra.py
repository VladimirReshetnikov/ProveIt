#!/usr/bin/env python3
"""Exact extrapolation identities and a deterministic estimator sanity check.

The synthetic path is a finite jump path, not a simulated Dirichlet Li--Levy
process. It checks implementation signs, normalization, and the angle inverse.
The analytic convergence theorems are proved in the paper.
"""
from fractions import Fraction
from math import comb, log, pi, sqrt
from pathlib import Path
import json
import numpy as np
from noisy_path_decoder import decode,weight_constants

ROOT=Path(__file__).resolve().parents[1]
identities=[]
for m in range(1,9):
    b=[(-1)**(j+1)*comb(m,j) for j in range(1,m+1)]
    assert sum(b)==1
    for r in range(1,m):
        assert sum(b[j-1]*j**r for j in range(1,m+1))==0
    total=sum(abs(c) for c in b)
    allocation=[Fraction(abs(c),total) for c in b]
    variance=sum(Fraction(c*c)/a for c,a in zip(b,allocation))
    assert variance==(2**m-1)**2
    identities.append({'m':m,'weights':b,'allocation':[str(a) for a in allocation],
                       'variance_factor_when_the_base_CLT_applies':int(variance),
                       'noiseless_root_mse_power':str(Fraction(m,4*m+3))})

T=20.0
heights=np.array([23.25,28.5,35.75])
signs=np.array([1.,-1.,1.])
jumps=signs*2*np.arctan(1/(2*heights))
increments=np.zeros(10000)
increments[[100,4000,8000]]=jumps
positions=np.concatenate(([0.],np.cumsum(increments)))
h=1e-4
result=decode(positions,h,[2,3,5],bandwidth=T)
normalizer,J=weight_constants()
weights=np.exp(-1/((heights/T-1)*(2-heights/T)))/normalizer
for p in [2,3,5]:
    expected=-pi*sqrt(p)/(T*log(p))*sum(weights*np.cos(heights*log(p)))
    actual=result['estimates'][str(p)]['estimate_real_character_value']
    assert abs(actual-expected)<1e-11
summary={'richardson_orders_checked':list(range(1,9)),
         'exact_identities':identities,'deterministic_decoder_check_passed':True,
         'weight_square_integral':J,
         'scope':'Algebra and implementation checks only; not a proof by simulation.'}
(ROOT/'results/analytic_checks.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='exact_identities'},indent=2))
