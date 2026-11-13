#!/usr/bin/env python3
"""Source inventory and bounded square-gap controls; never invokes Lean."""
from pathlib import Path
import hashlib,json,math,re
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
paths=[H/'MainSquareGap.lean',D/'Lean/DiophantineConsistency/Compact44/P72Root.lean',D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean',D/'research/ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean']
s=paths[0].read_text()
for name in ('no_main_square','two_ordinate_impossible'):
 assert re.search(r'\btheorem\s+'+name+r'\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
assert '(hbound : c<2*A)' in s and '(hDelta : A*A=Delta+1)' in s and 'P72Root.ι_tsub hac' in s
n=0
for A in range(2,50):
 for c in range(2,2*A):
  delta=A*A-1;z=1+delta*c*c
  assert (A*c-1)**2<z<(A*c)**2
  assert math.isqrt(z)**2!=z;n+=1
# Boundary c=1 gives a square, so the strict premise is necessary.
assert 1+(3*3-1)==3*3
print(json.dumps({'scope':'source inventory and finite controls only; no Lean invocation','gap_cases':n,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
