#!/usr/bin/env python3
"""Source inventory and finite Pell carrier controls; never invokes Lean."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
paths=[H/'CarrierGamma.lean',D/'Lean/DiophantineConsistency/ArithmeticHalfBinomialSandwich.lean',D/'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean',D/'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean',D/'Lean/DiophantineConsistency/ArithmeticPow.lean']
s=paths[0].read_text()
for n in ('gamma_gt_from_carrier','gamma_gt_from_modified_balance'):assert re.search(r'\btheorem\s+'+n+r'\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for text in ('(hR : 3≤R)','(hXa : X≤a)','(hwa : w≤a)','(hbal : d+H*W=','power_le_ycoord a (2:V)','x_gt a R'):
 assert text in s
cases=0
for a in range(15):
 for R in range(3,9):
  A=a+2;Delta=A*A-1;d,c=1,0
  for _ in range(R):d,c=A*d+Delta*c,d+A*c
  H0=4*a+3
  assert (2*a+3)**2<=c and d>(a+1)*c
  for X in range(a+1):
   for w in range(a+1):
    assert c>X+H0*w;cases+=1
# The index bound is meaningful: at R=2, the stated conclusion can fail.
a=4;R=2;X=w=4;H0=4*a+3;A=a+2;Delta=A*A-1;d,c=1,0
for _ in range(R):d,c=A*d+Delta*c,d+A*c
W=0;gamma=1
assert d+H0*W==X+a*c+H0*gamma and not (w<gamma)
print(json.dumps({'scope':'source inventory and finite controls only; no Lean invocation','growth_cases':cases,'R2_boundary':True,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
