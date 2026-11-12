#!/usr/bin/env python3
"""Source inventory and bounded carrier controls; never invokes Lean."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
paths=[H/'ModifiedCarrierFacts.lean',D/'Lean/DiophantineConsistency/Compact44/P72Power.lean',D/'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveMersenne2011.lean',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveMainOrientation2011.lean',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorThree2011.lean']
s=paths[0].read_text()
for n in ('modified_main_parts_positive','q4_from_modified_balance','modified_carrier_mod','modified_carrier_power','mersenne_divides_X','compact_beta_divides_X'):
 assert re.search(r'\btheorem\s+'+n+r'\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for text in ('(hU : 0<U)','(hY : q^3∣Y)','(hX16 : 16≤X)','(hdiv : q∣3*X)','CompactFixedBeta.beta_identity'):
 assert text in s
n=0;negative_difference=0
for q in range(1,9):
 for s0 in range(1,4):
  for X in range(1,5):
   Y=q**3*s0;U=q**5*s0;H0=3+4*Y*(X+1)
   for R in range(5):
    for W in range(5):
     for gamma in range(5):
      A=1+H0*max(W-gamma,0);d=A+H0*(gamma-W);k=R+1+U*W
      assert d>=0 and U*d+H0*k==U*A+H0*(U*gamma+R+1)
      assert (R+1-k)%q**4==0 and d%H0==A%H0
      negative_difference+=gamma<W;n+=1
# A factor-three case with q⁴ | k−R−1 but q⁵ not dividing it.
q=3;Y=27;X=1;H0=3+4*Y*(X+1);U=q**5;R=2;k=R+1+q**4;A=H0//3+1;d=1;gamma=0
assert U*d+H0*k==U*A+H0*(U*gamma+R+1)
assert (R+1-k)%q**4==0 and (R+1-k)%q**5!=0 and negative_difference>0
# Invalid unqualified cancellation: q=3 divides 3*2^R but not 2^R.
assert (3*2**7)%3==0 and (2**7)%3!=0
print(json.dumps({'scope':'source inventory and finite controls only; no Lean invocation','balance_cases':n,'negative_gamma_minus_W_cases':negative_difference,'factor_three_boundary':True,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
