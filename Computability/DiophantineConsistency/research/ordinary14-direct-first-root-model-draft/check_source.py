#!/usr/bin/env python3
"""Source inventory and finite arithmetic controls; never invokes Lean."""
from pathlib import Path
import hashlib,json,re
from itertools import product
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
paths=[H/'FirstRootBridge.lean',D/'Lean/DiophantineConsistency/Compact44/P72Root.lean',D/'Lean/DiophantineConsistency/Compact44/FreeJSumSquares.lean',D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean',D/'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean']
s=paths[0].read_text()
for n in ('fiveSquares_eq_zero_iff','root_of_scaled_residual','scaled_residual_of_root','positive_first_zero_iff'):
 assert re.search(r'\btheorem\s+'+n+r'\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
assert 'hM : 0<M' in s and 'hD : 0<D' in s and 'P72Root.ι_magnitude_sq' in s
for z in product(range(-2,3), repeat=5):
 assert (sum(x*x for x in z)==0)==all(x==0 for x in z)
for M in range(1,8):
 for P in range(7):
  for N in range(1,8):
   tau=abs(P-N)
   for d in range(1,20):
    assert ((M*M*((P-N)**2-d)==0)==(tau*tau==d))
    if tau*tau==d:
     old=P+tau
     assert old>0 and M*M*((P-old)**2-d)==0
print(json.dumps({'scope':'source inventory and finite controls only; no Lean invocation','sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
