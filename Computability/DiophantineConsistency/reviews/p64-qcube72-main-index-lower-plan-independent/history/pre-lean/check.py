#!/usr/bin/env python3
"""Finite controls over arbitrary small Y, including no q-cube assumption."""
import hashlib,json,math
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];P=ROOT/'Computability/DiophantineConsistency/research/p64-qcube72-main-index-lower-plan'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
parameters=0; indices=0;gcds=set()
for X in range(33,101):
 for Y in range(3,53):
  U=Y*Y;a=(X+1)*Y;H=4*a+3;e=math.gcd(U,H);mu=H//e
  assert 9%e==0 and H>9*X and e*mu==H and X<mu
  g,c=1,0;D=(a+1)*(a+3)
  for m in range(6):
   quotient,remainder=divmod(g-a*c-2**m,H)
   assert quotient>=0 and remainder==0 and 2**m<X and (U*(2**m-X))%H!=0
   g,c=(a+2)*g+D*c,g+(a+2)*c;indices+=1
  parameters+=1;gcds.add(e)
print(json.dumps({'status':'PASS_FINITE_CONTROLS','parameter_cases':parameters,'index_cases':indices,'observed_gcds':sorted(gcds),'scope':'Finite standard controls including Y not divisible by q³; no Lean or universal proof.','packet_readme_sha256':sha(P/'README.md'),'packet_check_sha256':sha(P/'check.py'),'review_script_sha256':sha(__file__)},sort_keys=True))
