#!/usr/bin/env python3
"""Independent exact audit of the degree-separated source certificate.
Does not import a builder. Source coefficient ports stay indeterminate.
"""
import sys
if sys.flags.optimize:
    raise RuntimeError('Run this exact audit without -O/-OO; assertions are part of the checker.')
import json,itertools,hashlib,math
from pathlib import Path
from collections import defaultdict
R=Path(__file__).resolve().parent
D=json.loads((R/'degree_channels.json').read_text())
P=R/'parent_quartic31.json'
S=json.loads(P.read_text());assert hashlib.sha256(P.read_bytes()).hexdigest()==D['parent_sha256']
C=D['certificate'];w=C['weights'];q=C['target_by_equation'];n=len(w);assert n==31 and len(set(w))==31 and min(w)>=1
assert max(w)==108 and max(q)==1914 and len(set(q))==22
exps={0:{(0,)*n:1},1:{},2:{}}
for i in range(n):
 a=[0]*n;a[i]=1;exps[1][tuple(a)]=1
 for j in range(i,n):
  a=[0]*n;a[i]+=1;a[j]+=1;exps[2][tuple(a)]=1 if i==j else 2
outputs={target:defaultdict(int) for target in q};checks=0
for d in range(3):
 records=D['channels'][str(d)];assert len({r['exponent'] for r in records})==len(records)
 for r in records:
  e=r['exponent'];assert e>=0
  for a,mult in exps[d].items():
   p=e+sum(x*y for x,y in zip(a,w));checks+=1
   if p in outputs:
    for x in r['recipe']:outputs[p][tuple(a)+tuple(x['powers'])]+=mult*x['coefficient']
for eq,target in zip(S['equations'],q):
 want=defaultdict(int)
 for t in eq['terms']:want[tuple(t['powers'])]+=2*t['coefficient']
 assert {x:y for x,y in outputs[target].items() if y}=={x:y for x,y in want.items() if y}
assert all(C['carrier_exponent']+sum(x*y for x,y in zip(a,w)) not in q for a in [(0,)*n]+list(exps[2]))
# Prove the asserted raw-coefficient majorant by exact integer arithmetic.
coefficient_checks={}
for name,instance in D['coefficient_instances'].items():
 ell=instance['port_bitlengths']; M=1<<instance['M_exponent']; sizes=[]
 for records in D['channels'].values():
  for r in records:
   v=sum(abs(t['coefficient'])*(1<<sum(a*b for a,b in zip(t['powers'],ell))) for t in r['recipe'])
   assert v<M;sizes.append(v.bit_length())
 assert max(sizes)==instance['M_exponent']
 assert instance['kappa']%2==0 and instance['kappa']>=instance['M_exponent']+13
 coefficient_checks[name]={'max_majorant_bitlength':max(sizes),'kappa':instance['kappa']}
# Finite regression of the universal borrow-digit step.
cases=0
for B in (8,16,32,64,128):
 for h in range(-B//4+1,B//4):
  for incoming in (-1,0):
   z=2*h+1+incoming;digit=z%B;out=z//B
   assert out in (-1,0)
   assert (digit&(B-2)==0)==(h==0)
   cases+=1
# Exact parity calibration exponents; holds symbolically for every k.
W=C['W'];Q=C['Q'];K=Q+1+2*W;E=K+W+2;H=E+W+23;kappa=2134940
assert (W,Q,K,E,H)==(108,1914,2131,2241,2372)
for k in range(1,65):
 v=kappa+2*k;u=2+k+E*v;popT=(W+23)*v-31*k-22
 logN=8*kappa-10+k+1178*v
 assert u+popT==2*logN
result={'status':'pass','exact_source_identities':22,'interaction_checks':checks,'raw_records':94,'quadratic_expansion_monomials':496,'linear_expansion_monomials':31,'borrow_regression_cases':cases,'W':W,'Q':Q,'K':K,'E':E,'H':H,'coefficient_checks':coefficient_checks,'formal_status':'exact finite audit; unbounded theorems proved in CHANNEL_PROOF.md'}
(R/'CHANNEL_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
