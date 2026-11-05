#!/usr/bin/env python3
"""Finite controls over arbitrary small Y, including no q-cube assumption."""
import hashlib,json,math
from pathlib import Path
P=Path(__file__).resolve().parent/'history/pre-lean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
old=json.loads((P/'result.json').read_text())
assert sha(P/'packet-README.md')==old['packet_readme_sha256']
assert sha(P/'packet-check.py')==old['packet_check_sha256']
assert sha(P/'check.py')==old['review_script_sha256']
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
print(json.dumps({'status':'PASS_FINITE_CONTROLS','parameter_cases':parameters,'index_cases':indices,'observed_gcds':sorted(gcds),'scope':'Historical pre-Lean packet; finite standard controls including Y not divisible by q³; no Lean or universal proof.','packet_readme_sha256':sha(P/'packet-README.md'),'packet_check_sha256':sha(P/'packet-check.py'),'review_script_sha256':sha(__file__)},sort_keys=True))
