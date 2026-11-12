#!/usr/bin/env python3
"""Bounded source inventory and arithmetic controls; never invokes Lean."""
from pathlib import Path
import hashlib,json,math,re
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
paths=[H/'AuxRootBounds.lean',D/'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean',D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean',D/'research/ordinary14-aux-root-model-draft/AuxRootBridge.lean']
s=paths[0].read_text()
for name in ('first_ordinate_large','strong_f_square_large','strong_Q_gt_one','signed_square_gt_one'):
 assert re.search(r'\btheorem\s+'+name+r'\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
assert '(hk : 2<k)' in s and '(hDeltaSmall : Delta<c*c*c)' in s and '(hc : 1<c)' in s
pell=0;strong=0;gap=0
for m in range(1,51):
 for k in range(3,601):
  tau=math.isqrt(1+m*(m+1)*k*k)
  if tau*tau==1+m*(m+1)*k*k:pell+=1;assert k>=8*m+4
for c in range(2,9):
 for delta in range(1,c**3):
  for i in range(1,5):
   for f in range(1,31):
    I=i*c*c
    if I*I+delta==delta*f*f:
     strong+=1;assert f*f>c+1 and I*I>1
for c in range(2,16):
 for f in range(1,15):
  if f*f<=c+1:continue
  for t in range(-4,5):
   z=f*f*t-c;gap+=1;assert z*z>1
assert pell>0 and strong>0 and gap>0
print(json.dumps({'scope':'source inventory and bounded controls only; no Lean invocation','pell_cases':pell,'strong_cases':strong,'gap_cases':gap,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
