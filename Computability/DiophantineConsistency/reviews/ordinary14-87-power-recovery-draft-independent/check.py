#!/usr/bin/env python3
"""Independent 87 source interface review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-power-recovery-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'PowerRecovery87.lean','a4d59f432ba00afde8fe319a14f18d35d52117caac89719d0fda938a681e6d94').decode()
pin(A/'check_source.py','9866a56df3b7c3eec05cc4bb8d13d305584c8b95af3784c3f2279b05728f6700')
receipt=pin(A/'observation.json','dda1eb05a7e6bc7c5472209318dc2d834ce0f705953ff6850c88ac14dc244fba')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n' b'`../../reviews/ordinary14-87-power-recovery-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='f4ce58b4d02c40e1cf413e01866a6a2576696e622d30087b631bb9d841a2b009'
for f in ['(hbeta46 : 46≤beta)', 'P72ExactIndices87Draft.exact_indices p beta K MC MF v', 'FirstQuotient87Draft.quotient_and_root', 'let W : V := 4*xx*qq*s0*s', 'H*(xx*yy*qq)', 'have hH : H=3+qq*D', 'projection_quotient aa R', 'have h3mod : (3*xx)%H=(3*Exp.exp R)%H', 'Growth87Draft.growth p beta K MC MF v', 'rw [mod_eq_self_of_lt h3X,mod_eq_self_of_lt h3exp] at h3mod']:assert f in s,f
n=0
for a in range(1,40):
 H=4*a+3
 for X in range(a):
  for Z in range(a):
   if (3*X-3*Z)%H==0:
    assert X==Z;n+=1

def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
p=D/'reviews'/'ordinary14-87-growth-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero source interface review; no Lean','finite_controls':n},sort_keys=True,indent=2))
