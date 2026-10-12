#!/usr/bin/env python3
"""High-precision Gamma quadrature cross-check of the three-face term."""
import itertools,json,time
from pathlib import Path
import mpmath as mp
mp.mp.dps=45
A=mp.mpf(2)
MASSES=tuple(map(mp.mpf,('0.2','0.7','1.3')))

def first(B):
    return 2*mp.re(mp.loggamma(A+1j*mp.sqrt(B)))-2*mp.loggamma(A)

def triangle(order):
    nodes,weights=mp.gauss_quadrature(order,'legendre')
    nodes=[(x+1)/2 for x in nodes]
    weights=[x/2 for x in weights]
    verts=[first(B) for B in MASSES]
    total=mp.mpf(0)
    for perm in itertools.permutations(range(3)):
        Bs=[MASSES[i] for i in perm]
        fs=[verts[i] for i in perm]
        for u,wu in zip(nodes,weights):
            for v,wv in zip(nodes,weights):
                denom=1+u+u*v
                ts=[1/denom,u/denom,u*v/denom]
                H=first(sum(t*B for t,B in zip(ts,Bs)))+sum(t*f for t,f in zip(ts,fs))
                for i,j in itertools.combinations(range(3),2):
                    tij=ts[i]+ts[j]
                    H-=tij*first((ts[i]*Bs[i]+ts[j]*Bs[j])/tij)
                total+=wu*wv*H/(u*v)
    return total

base=json.loads(Path(__file__).with_name('verification_faces.json').read_text())
direct=mp.mpf(base['direct_delta3_85_17'])
row=base['face_formula'][-1]
I=mp.mpf(row['sum_pair_I_E2'])
J=mp.mpf(row['sum_pair_J_E1'])
results=[]
for order in (16,24,32):
    start=time.monotonic()
    T=triangle(order)
    ans=-9*I-6*J-6*T
    data={'order':order,'triple_integral':mp.nstr(T,43),'delta3_faces':mp.nstr(ans,43),
          'error_vs_direct_spectrum':mp.nstr(abs(ans-direct),8),'elapsed_seconds':round(time.monotonic()-start,2)}
    results.append(data)
    print(json.dumps(data),flush=True)
Path(__file__).with_name('verification_faces_high_precision.json').write_text(json.dumps(results,indent=2)+'\n')
