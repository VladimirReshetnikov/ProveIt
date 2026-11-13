#!/usr/bin/env python3
"""Source inventory and finite geometric controls; never invokes Lean."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
paths=[H/'AuxGeometry.lean',D/'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean',D/'research/ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean',D/'research/ordinary14-model-main-square-gap-draft/MainSquareGap.lean']
s=paths[0].read_text();assert re.search(r'\btheorem\s+geometry_of_large_k\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
assert '(hk : 8*X*Y*Y+4≤k)' in s and '(hDelta :' in s and '(hY : 0<Y)' in s
n=0
for X in range(0,12):
 for Y in range(1,12):
  for eta in range(1,6):
   for extra in range(3):
    k=8*X*Y*Y+4+extra;A=X*Y+Y+2;c=eta+Y*k;delta=A*A-1
    assert A<c and 1<c and 0<delta<c*c*c;n+=1
# Without the large-k bound, the c>A implication can fail.
assert 3*1+1+2>=1+1*1
print(json.dumps({'scope':'source inventory and finite controls only; no Lean invocation','geometry_controls':n,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
