#!/usr/bin/env python3
"""High-precision diagnostics, not certificates, for large-N Euler budgets.

The a=0 values use the finite Euler sum and beta/eta at high precision.
Positive-a values replace g by E_512; the proved 5/4 remainder bound
makes the resulting scaled truncation error at most (5/4) 2^(N-512).
"""
import json
from math import comb
from pathlib import Path
import mpmath as mp

mp.mp.dps = 210
NS = [4, 16, 64, 256]
weights = {}
for N in NS:
    weights[N] = [sum(comb(j,n) * 2**(N-j-1)
                      for j in range(n,N)) for n in range(N)]

def axis_C(b):
    beta = mp.power(4,-b)*(mp.zeta(b,mp.mpf(1)/4)-mp.zeta(b,mp.mpf(3)/4))
    eta = (1-mp.power(2,1-b))*mp.zeta(b)
    return beta + mp.power(2,-b)*eta

def axis_R(N,b):
    harm=mp.mpf(0)
    terms=[]
    for n in range(1,N):
        harm += mp.power(2*n-1,-b)+mp.power(2*n,-b)
        terms.append((-1)**n*weights[N][n]*harm)
    return mp.fsum(terms)+mp.power(2,N-1)*axis_C(b)

def positive_R(N,a,b,M=512):
    harm=mp.mpf(0)
    diffs=[mp.mpf(0)]
    for n in range(1,M):
        harm += mp.power(2*n-1,-b)+mp.power(2*n,-b)
        diffs.append(harm/mp.power(2*n+1,a))
    tail=[]
    for j in range(M):
        if j >= N:
            tail.append(-diffs[0]*mp.power(2,N-j-1))
        diffs=[diffs[k]-diffs[k+1] for k in range(len(diffs)-1)]
    return mp.fsum(tail)

def decimal(x):
    return mp.nstr(x,35)

p=mp.log(2)/mp.log(mp.mpf(3)/2)
q=mp.log(3)/mp.log(2)
c=(1-1/q)*q**(-p)
rows=[]
for N in NS:
    bhat=mp.log(N*q)/mp.log(mp.mpf(3)/2)
    dr=lambda b:mp.diff(lambda s:axis_R(N,s),b)
    bopt=mp.findroot(dr,(bhat-1,bhat),tol=mp.mpf('1e-35'),maxsteps=30)
    pred=c*N**(-p)
    row=dict(N=N,b_hat=decimal(bhat),axis_stationary_b=decimal(bopt),
             axis_R_at_bhat=decimal(axis_R(N,bhat)),
             axis_R_at_stationary_b=decimal(axis_R(N,bopt)),
             predicted_excess=decimal(pred),
             bhat_excess_ratio=decimal((axis_R(N,bhat)-1)/pred),
             stationary_excess_ratio=decimal((axis_R(N,bopt)-1)/pred))
    row['positive_a_at_bhat']=[dict(a=str(a),R=decimal(positive_R(N,mp.mpf(a),bhat)))
                                    for a in ['0.0001','0.01','0.1']]
    row['positive_a_scaled_truncation_bound']=decimal(mp.mpf('1.25')*mp.power(2,N-512))
    rows.append(row)
    print(json.dumps(row),flush=True)
result=dict(status='DIAGNOSTIC_ONLY',precision_digits=mp.mp.dps,
            p=decimal(p),q=decimal(q),c=decimal(c),
            note='Stationary points are numerical roots, not certified global optima.',rows=rows)
(Path(__file__).resolve().parents[1]/'data'/'axis_remainder_diagnostics.json').write_text(json.dumps(result,indent=2)+'\n')
