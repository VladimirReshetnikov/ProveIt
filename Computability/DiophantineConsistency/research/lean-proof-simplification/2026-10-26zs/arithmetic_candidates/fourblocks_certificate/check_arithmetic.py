"""Non-Lean checks only. These do NOT validate Lean elaboration or kernel checking."""
import json
from pathlib import Path
import sympy as s

def require(condition, message="Required check failed"):
    if not condition:
        raise RuntimeError(message)

q,C,F,MC,MF,J,beta=s.symbols('q C F MC MF J beta')
four=(C-1)+(MC*J+1)+q*(F+(MF*J-1))+q**2*(q-C)+q**3*(q-F-1)
rank=(q*(q-F)-C)*(q**2-1)+(MC+q*(MF+beta))*J
residual=s.expand(four-rank)
certificate=s.expand(-q*(beta*J+1-q))
require(s.expand(residual - certificate) == 0)
cases=0
for b in range(1,9):
 for j in range(1,5):
  Q=b*j+1
  for c in range(1,Q):
   for f in range(Q-c):
    for mc in (0,1,3):
     for mf in (1,2,5):
      # Every domain used by push_cast is checked before ordinary evaluation.
      require(1 <= c and 1 <= mf * j and (c <= Q) and (f <= Q) and (1 <= Q - f))
      v=(c-1)+(mc*j+1)+Q*(f+(mf*j-1))+Q**2*(Q-c)+Q**3*(Q-f-1)
      r=(Q*(Q-f)-c)*(Q**2-1)+(mc+Q*(mf+b))*j
      require(v == r)
      cases+=1
# Missing the MF*J>=1 cast guard invalidates the ordinary integer expansion.
Q,c,f,mc,mf,b,j=4,1,0,0,0,3,1
nat=lambda x:max(0,x)
v=nat(c-1)+(mc*j+1)+Q*(f+nat(mf*j-1))+Q**2*nat(Q-c)+Q**3*nat(nat(Q-f)-1)
r=(Q*(Q-f)-c)*(Q**2-1)+(mc+Q*(mf+b))*j
require(v != r)
out={'status':'PASS: non-Lean algebra/samples only; Lean UNCOMPILED','symbolic_residual':str(s.factor(residual)),'certificate':'-(q : ℤ) * (beta*J + 1 - q)','sample_cases':cases,'negative_domain_guard_case':{'q':Q,'C':c,'F':f,'MC':mc,'MF':mf,'beta':b,'J':j,'fourBlocks_nat':v,'rank_int':r}}
print(json.dumps(out,indent=2))
Path(__file__).with_name('arithmetic_checks.json').write_text(json.dumps(out,indent=2)+'\n')
