from pathlib import Path
from hashlib import sha256
import json,random
p=Path('research/ordinary13-eta-zero-direct-projection-model-draft')
fs=[p/'EtaZeroDirectProjection.lean.src',p/'README.md',
Path('Lean/DiophantineConsistency/Compact44/DirectMainProjection.lean'),
Path('Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean'),
Path('research/ordinary13-eta-zero-early-congruence-model-draft/EtaZeroEarlyCongruence.lean.src'),
Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json')]
s=[f.read_text() for f in fs]
for x in ['power_of_direct_carrier','(hq : 0<q)','(hs : 0<s)','(hindex :','(hcar :','(hbound :',
 '(hx :','(hy :','let W := 4*X*q*s*w','DirectMainProjection.direct_projection','projection_quotient']:
 assert x in s[0],x
assert 'theorem direct_projection' in s[2] and 'theorem projection_quotient' in s[3]
rng=random.Random(2371)
for _ in range(600):
 q=rng.randrange(1,10); X=rng.randrange(12); st=rng.randrange(1,6); w=rng.randrange(8)
 Y=q**3*st; U=Y*q*q; W=4*X*q*st*w; a=X*Y+Y; H=3+4*a
 R,c,gamma,main=(rng.randrange(10) for _ in range(4))
 k=R+1+4*X*Y*Y*w
 assert 4*X*Y*Y*w==U*W
 defect=U*main+H*k-U*(X+a*c)-H*(U*gamma+R+1)
 assert defect==U*(main+H*W-(X+a*c+H*gamma))
for a in range(12):
 x,y=1,0;H=4*a+3
 for R in range(12):
  numerator=x-2**R-a*y
  assert numerator>=0 and numerator%H==0
  x,y=(a+2)*x+(a+1)*(a+3)*y,x+(a+2)*y
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'carrier_defect_controls':600,'pell_projection_controls':144,
 'lean_executed':False,'proof_status':'unelaborated; graph and witness extraction remain open'},sort_keys=True,indent=2))
