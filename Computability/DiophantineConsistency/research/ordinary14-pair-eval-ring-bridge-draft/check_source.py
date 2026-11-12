#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
paths=[P/'PairEvalRingBridge.lean',D/'research/ordinary14-five-unit-model-facts-draft/FiveUnitFacts.lean',D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean',D/'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorMagnitude2011.lean']
s=paths[0].read_text()
for t in ('split_evalRing','evalSemiring_map','ι_injective','(hp : Equivalent p p\')','equivalent_multiply','five_positive_of_direct_first','(hm : 2≤m)','(hq : pairResidue q ≠ -1)','(ht : pairResidue t ≠ -1)'):
 assert t in s,t
pairs=list(product(range(3),repeat=2)); sample=[(0,0),(1,0),(0,1)]
def val(p):return p[0]-p[1]
def mul(a,b):return (a[0]*b[0]+a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def chain(p,q,r,s0,t):
 for z in (q,r,s0,t):p=mul(p,z)
 return p
controls=0;both=0
for p,p1 in product(pairs,repeat=2):
 if val(p)!=val(p1):continue
 for q,r,s0,t in product(sample,repeat=4):
  x=chain(p,q,r,s0,t);y=chain(p1,q,r,s0,t)
  assert val(x)==val(y)
  for u in sample:
   assert (val(x)==val(u)) == (val(y)==val(u))
   if val(x)==val(u):both+=1
   controls+=1
assert both>0
print(json.dumps({'scope':'finite signed-pair arithmetic and source signature controls only; no Lean, graph evaluation or model endpoint','files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},'equivalence_controls':controls,'true_product_equivalences':both},sort_keys=True,indent=2))
