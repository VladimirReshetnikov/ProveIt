#!/usr/bin/env python3
"""Exact checks for the proposed 70-gate sphere's negative transport branch."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import hashlib, json
from pathlib import Path

def need(ok, msg):
    if not ok: raise RuntimeError(msg)

# Symbolic expressions in Z[b,K,w], as exact sparse exponent maps.
def norm(x): return {m:c for m,c in x.items() if c}
def add(x,y):
    z=x.copy()
    for m,c in y.items(): z[m]=z.get(m,0)+c
    return norm(z)
def neg(x): return {m:-c for m,c in x.items()}
def mul(x,y):
    z={}
    for a,ca in x.items():
        for b,cb in y.items():
            k=tuple(i+j for i,j in zip(a,b));z[k]=z.get(k,0)+ca*cb
    return norm(z)
one={(0,0,0):1}; b={(1,0,0):1}; K={(0,1,0):1}; w={(0,0,1):1}
q=add(b,one); F=add(one,one); alpha=add(b,neg(one)); z=one
qF=add(q,neg(F)); C=add(qF,neg(alpha))
W=add(add(mul(add(K,w),C),qF),neg(mul(z,b)))
need(C=={},'C must vanish identically')
need(W==neg(one),'W must equal -1 identically')
# On the abstract norm tuple (1,1,1,1,-1), the proposed equation vanishes
# and the old 71-operation sphere equals 4. This is not a full graph zero.
P=Q=U=Z=1; Wv=-1
old=(P*Q)**2+(U*Wv-1)**2+Z**2-2
new=(P*Q)**2+(U*Wv)**2+Z**2-3
need(old==4 and new==0,'negative unit discrepancy')
count=0
for beta in range(1,9):
    for J in range(1,9):
        b0=beta*J
        if b0<2: continue
        for K0 in range(1,8):
            for w0 in range(1,8):
                q0=b0+1; F0=2; alpha0=b0-1; z0=1
                C0=q0-F0-alpha0
                W0=(K0+w0)*C0+q0-F0-z0*b0
                need(all(t>0 for t in (beta,J,K0,w0,F0,alpha0,z0)) and C0==0 and W0==-1,'control')
                count+=1
print(json.dumps({'status':'PASS','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'symbolic_transport':'C=0 and W=-1 identically over Z[b,K,w]',
    'old_on_abstract_tuple':old,'new_on_abstract_tuple':new,'positive_transport_controls':count,
    'scope':'transport-only and abstract norm controls; no full graph zero or existence-equivalence claim'},sort_keys=True,indent=2))
