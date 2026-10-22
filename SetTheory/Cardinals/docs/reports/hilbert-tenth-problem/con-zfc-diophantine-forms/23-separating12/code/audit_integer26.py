#!/usr/bin/env python3
"""Independent quotient-algebra audit of the 26-integer circuit."""
from pathlib import Path
import argparse
import hashlib
import itertools
import json
import math

ap=argparse.ArgumentParser()
ap.add_argument('--source',type=Path,default=Path(__file__).resolve().parents[1]/'data/integer26/polynomial26.json')
ap.add_argument('--out',type=Path,default=Path(__file__).resolve().parents[1]/'data/integer26_independent_checks.json')
args=ap.parse_args()
SOURCE=args.source.resolve()
packet=json.loads(SOURCE.read_text())

def eval_dag(values):
    env=dict(values)
    for g in packet['gates']:
        left,right=(env[a] if isinstance(a,str) else a for a in g['args'])
        env[g['name']]=(left+right if g['op']=='+' else
                        left-right if g['op']=='-' else left*right)
    return env

def ring_product(x,y,A,S):
    # Basis indexed by the bits of r^j u^k, with r^2=A, u^2=S.
    z=[0]*4
    for j,k in itertools.product(range(4),repeat=2):
        factor=(A if j&k&1 else 1)*(S if j&k&2 else 1)
        z[j^k]+=x[j]*y[k]*factor
    return z

def norm_check(e):
    A,S=e['Aroot'],e['Sroot']
    ell=[e['H']*e['t']+e['weightN']*e['P'],
         -e['H']*e['weightM'],-e['weightN'],0]
    x=[e['d']*v for v in ring_product(ell,ell,A,S)]
    x[0]-=e['H']**2*e['e']
    f=ring_product(x,x,A,S)
    B=2*e['Qstrong']*e['v']*e['b']
    f[0]-=e['H']**4*B**2*e['D']
    fu=[v if j&2==0 else -v for j,v in enumerate(f)]
    g=ring_product(f,fu,A,S)
    assert g[2:]==[0,0]
    gr=[v if j&1==0 else -v for j,v in enumerate(g)]
    n=ring_product(g,gr,A,S)
    assert n[1:]==[0,0,0]
    assert n[0]==e['Norm26']

records=[]
for w,s,T in itertools.product((0,1,-2),(-2,0,3),(-2,0,2)):
    vals={v:0 for v in packet['variables']}
    vals.update(beta=15,kappa=19,MC=2,MF=20,
        J__u=3,w_integer=w,s_integer=s,T=T,h=-1,t=2)
    e=eval_dag(vals)
    norm_check(e)
    assert e['Aroot']>=1 and e['Sroot']>1
    assert e['Delta']>e['R']>0
    assert 1<e['b']<e['Qstrong']-1
    assert math.gcd(e['H'],e['d'])==1
    assert math.gcd(e['H'],e['weightN'])==1
    ycap=2*(abs(e['v'])*(math.isqrt(e['D'])+1)+e['b'])
    assert e['weightM']>ycap
    maincap=e['weightM']*(math.isqrt(e['Aroot'])+1)+ycap
    assert e['weightN']**2*e['Sroot']>e['H']**2*maincap**2
    records.append(dict(w=w,s=2*s+1,T=T))

result=dict(status='passed',source='data/integer26/polynomial26.json',
    source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    quotient_algebra_tests=len(records),cases=records,
    method='Generic multiplication in Z[r,u]/(r^2-A,u^2-S), conjugation twice; no copied scalar norm formulas.',
    includes_T_zero=True,includes_X_zero=True,includes_negative_s=True,
    exact_metrics=dict(unknowns=len(packet['variables']),operations=len(packet['gates']),
                       degree=packet['exact_total_degree']),
    scope='Finite arithmetic audit; general soundness is established in the separate mathematical proof.')
args.out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))
