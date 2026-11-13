#!/usr/bin/env python3
"""Independent 87 source interface review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-first-index-modq4-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'FirstIndexModQ487.lean','3961385c35ac28b1f541b1f003076fe0e9ab70f5937068e1e945571088111263').decode()
pin(A/'check_source.py','85d749e9ab01da45950b8e180163595c6e543481f36c5e06ca3e87bbf5dec101')
receipt=pin(A/'observation.json','aceda2668a8708a7858087f4749871089b2ad7abe46a78acf46ebc3a8ba8fc0b')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n' b'`../../reviews/ordinary14-87-first-index-modq4-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='f6e43ea938e48ec6a28ac050e2adade5b8b1f0e29fbb1216002dac0ee71feca2'
for f in ['FirstIndex87Draft.index_residues p beta v', 'Q4Rank87Draft.q4_rank p beta K MC MF v', 'magnitude_mod (R+1,k v) (qq^4) hm hmag', 'refine ⟨4*(v 6)*qq^2*(s*s)*w,?_⟩', "hmod'.symm"]:assert f in s,f
ncase=0
for q in range(2,11):
 for X in range(1,5):
  for quotient in range(1,5):
   Y=q**3*quotient; m=X*Y*Y
   for w in range(5):
    for n in range(1,6):
     k=2*n+4*m*w; R=2*n+q**4-1
     assert (4*m*w)%q**4==0 and (R+1)%q**4==k%q**4==2*n%q**4;ncase+=1
n=ncase

def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
for name in ['ordinary14-87-first-index-draft-independent', 'ordinary14-87-q4-rank-draft-independent']:
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero source interface review; no Lean','finite_controls':n},sort_keys=True,indent=2))
