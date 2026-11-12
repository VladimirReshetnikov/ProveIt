#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'QuotientFacts.lean').read_text()
for t in ('scaled_quotient M (magnitude z) D hM hsq','magnitude_mod z Q hQ hQdiv','Bez b Q 1','unit_certificate_cancel hunit hby','0<s ∧ Y=Q*s ∧ 0<tau ∧ tau*tau=D'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
count=0;signs={1:0,-1:0}
for b in range(1,5):
 Q=(1+b)**3;M=Q*b
 for Y in range(1,151):
  for pp in range(1,7):
   for rr in range(1,7):
    z=M*(pp-rr)+b*Y
    if z and z%M==0:
     tau=abs(z)//M;assert Y%Q==0 and tau>0 and z*z==M*M*tau*tau
     signs[1 if z>0 else -1]+=1;count+=1
assert all(signs.values()) and count>0
paths=[P/'QuotientFacts.lean',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFirstDivisibility2011.lean',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean',D/'Lean/DiophantineConsistency/ArithmeticGcdNormalization.lean',D/'Lean/DiophantineConsistency/Compact44/P72Root.lean']
print(json.dumps({'scope':'source interface inventory and finite signed-root controls; no Lean invocation','finite_qualifying_cases':count,'sign_counts':signs,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
