#!/usr/bin/env python3
"""Floating-point diagnostics for the explicit proved remainder majorant.
These values are illustrative, not interval-certified. Only standard Python.
"""
import csv, math
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
Ns=[100,300,1000,3000,10000,30000,100000]
logc=[0.0]*(max(Ns)+1); ratio=1.0
for n in range(3,len(logc)):
    ratio=(3*(2*n-3)-(n-3)/ratio)/n
    logc[n]=logc[n-1]+math.log(ratio)
rho=3-2*math.sqrt(2);r0=0.05
rows=[]
for N in Ns:
    vals=[N*math.log(1/rho)-math.log(1-r0/rho)]
    ks=[N]
    for k in range(2,N):
        vals.append(logc[k]+(N-k)*math.log(k*(k-1))-math.lgamma(N-k+1));ks.append(k)
    mx=max(vals); i=vals.index(mx)
    logM=mx+math.log(math.fsum(math.exp(v-mx) for v in vals))
    rows.append([N,logM,(logM-N*math.log(N)+2*N*math.log(math.log(N)))/N,
                 ks[i],ks[i]*math.log(N)/N])
with (ROOT/'data'/'majorant_diagnostics.csv').open('w') as f:
    w=csv.writer(f);w.writerow(['N','log_M_N','centered_per_N','maximizing_block_k','k_logN_over_N']);w.writerows(rows)
for row in rows:print(row)
