#!/usr/bin/env python3
"""Source inventory and finite auxiliary controls; never invokes Lean."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
paths=[H/'AuxRootBridge.lean',D/'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean',D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean']
s=paths[0].read_text()
for n in ('oldAux_eq_direct','square_gt_of_aux','positive_of_above','above_of_positive','positive_aux_coordinate_iff'):
 assert re.search(r'\btheorem\s+'+n+r'\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
assert '(hQ : 1<Q)' in s and '(hz : 1<z*z)' in s
n=0;positive_old=0;positive_new=0
for Q in range(2,13):
 for z in range(-50,51):
  if z*z<=1:continue
  for y in range(-100,101):
   if y*y-Q*(y*y-z*z)!=1:continue
   n+=1;assert y*y>z*z
   if y>z:
    positive_old+=1;assert y>0 and y-z>0
   if y>0:
    positive_new+=1;assert y>z and y-z>0
assert n>0 and positive_old>0 and positive_new>0
# Without z²>1 the strict witness conclusion can fail (Q=4,z=y=1).
assert 1-4*(1-1)==1 and not (1>1)
print(json.dumps({'scope':'source inventory and finite controls only; no Lean invocation','norm_cases':n,'positive_old_cases':positive_old,'positive_new_cases':positive_new,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
