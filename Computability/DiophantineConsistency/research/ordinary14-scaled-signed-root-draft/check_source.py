#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
s=(H/'SignedScaledRoot.lean').read_text()
for x in ('nonneg_or_nonpos Z','scaled_quotient U z n hU hsq','Z=ι (U*d) ∨ Z= -ι (U*d)'):assert x in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
n=0
for u in range(1,9):
 for d in range(9):
  for sign in (-1,1):
   z=sign*u*d; assert z*z==u*u*d*d and (z==u*d or z==-u*d);n+=1
paths=[H/'SignedScaledRoot.lean',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean',D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean']
print(json.dumps({'scope':'source interface inventory and integer controls only; no Lean invocation','integer_controls':n,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
