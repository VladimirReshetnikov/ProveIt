#!/usr/bin/env python3
"""Independent 87 own-zero q³ size source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-qcube-size-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'QCubeSize87.lean','8af3af947084ded2ed389f3d3598fe0a7548c8f66c79cd260241937783be555d').decode()
pin(A/'check_source.py','addb3977c996b2467bcddf865b41f839e6b5225694855ee586cc925f11b28632')
receipt=pin(A/'observation.json','22c5c511fa65ecbbd37ed9d829f909139ed1565d5bd71c0c349c605793c77c6c')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-87-qcube-size-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='c8eaaf29281642e9e4141dde3cee8e3916f1c8f641b131ba50a8dbf7af29e953'
for f in ('FirstQuotient87Draft.quotient_and_root p beta v hbeta hJ hY hport hz',
 'let u := Function.update v 7 s','have hJ\' : 0<u 0','have hs\' : 0<u 7',
 'QCubeSize84Draft.Y_at_least_eight beta u hbeta hJ\' hs\'',
 'rw [hYq]'):
 assert f in s,f
assert 'InternalZero (P86ResidueGraph.graph p).output' not in s
n=0
for beta in range(1,12):
 for J in range(1,12):
  for quotient in range(1,12):
   q=1+J*beta;Y=q**3*quotient
   assert Y>=8;n+=1
def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
for name in ('ordinary14-87-first-quotient-draft-independent','ordinary14-84-qcube-size-draft-independent'):
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero quotient-to-size source review; no Lean','bounded_size_cases':n},sort_keys=True,indent=2))
