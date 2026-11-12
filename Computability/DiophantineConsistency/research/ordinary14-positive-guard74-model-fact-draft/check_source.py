#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
paths=[P/'Guard74Strict.lean',D/'Lean/DiophantineConsistency/DiscreteOrderedRingFacts.lean',D/'research/ordinary14-positive-guard74/README.md']
s=paths[0].read_text()
for token in ('(hd : Discrete R)','(hF : 0<F)','(halpha : 0<alpha)','(hX : 0<X)','(hK : 0≤K)','(hXq : q≤X)','(hh : 1≤h)','(hguard : (q-F-alpha)*(X+K)-F=b*(h-1))'):
 assert token in s,token
count=0
for q in range(1,8):
 for F,alpha in product(range(1,8),repeat=2):
  for X,K,b,h in product(range(q,q+3),range(3),range(-2,3),range(1,4)):
   if (q-F-alpha)*(X+K)-F == b*(h-1):
    assert h>1
    count+=1
assert count>0
q,F,alpha,X,K,h=5,3,1,1,2,1
assert X<q and (q-F-alpha)*(X+K)-F==0
print(json.dumps({'scope':'finite controls and source-signature checks only; no Lean, graph binding or provider proof','files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},'guard_equality_cases':count,'x_ge_q_necessary_partial_control':[q,F,alpha,X,K,h]},sort_keys=True,indent=2))
