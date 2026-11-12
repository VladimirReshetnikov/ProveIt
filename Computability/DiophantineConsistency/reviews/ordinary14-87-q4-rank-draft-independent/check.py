#!/usr/bin/env python3
"""Independent 87 source interface review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-q4-rank-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'Q4Rank87.lean','126ff2a2d2a6339b4d936c2c0a43463e5815e83da892032d095bd087fd874f7a').decode()
pin(A/'check_source.py','598268e538dd631e2dbfcfb15c8e37807e3cb7acfae69059ca56d7fb1fb0c67e')
receipt=pin(A/'observation.json','a16feaecf4a8e8ce2053ba9a9780f192b3c87318a82ff3f463369ab1f882d963')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n' b'`../../reviews/ordinary14-87-q4-rank-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='e9d28cb536117d7f87e4e6fe707eeac8c69d5d2a62fc3b1e50deb873cdb9b57c'
for f in ['FirstQuotient87Draft.quotient_and_root', 'have hU : uu=qq^5*s', 'MainBalance87Draft.norm_and_balance', 'xx*yy*qq+(R+1)', 'q4_rank_from_balance qq yy xx R kk']:assert f in s,f
import math
n=0
for q in range(2,25):
 for s in range(1,6):
  for X in range(1,8):
   Y=q**3*s; H=3+4*Y*(X+1); g=math.gcd(H,q**5)
   assert 3%g==0 and (q**5//g)%q**4==0
   assert (X*Y*q)%q**4==0; n+=1

def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
for name in ['ordinary14-87-main-balance-conditional-draft-independent', 'ordinary14-87-qcube-size-draft-independent']:
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero source interface review; no Lean','finite_controls':n},sort_keys=True,indent=2))
