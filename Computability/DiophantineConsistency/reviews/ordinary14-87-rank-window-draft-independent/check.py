#!/usr/bin/env python3
"""Independent 87 source interface review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-rank-window-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'RankWindow87.lean','76ba5dee4ca6ae81eac40f0fbef9c324f66e433644d66fa347d5d4443bf2826e').decode()
pin(A/'check_source.py','64111daca205c3d5da9667945eba135c7bd8d0e9bf32282268232663b7c316e5')
receipt=pin(A/'observation.json','f632a8fd7567bb0a90c1f34559b1817e3e10eba1facabf72bfba9448ca7a4945')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n' b'`../../reviews/ordinary14-87-rank-window-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='9265176abf799e0aa6c47ec419168e9805610569eaffcd9575a603e9dd4a2c97'
for f in ['(hMC : MC<beta) (hMF : MF<2*beta)', 'gap_of_87_zero p beta K v hport hK (hv 1) (hv 6) hz', 'scalar_rank_window q beta MC MF', 'RankLower4084Draft.scalar_lower40 q beta', '40≤R ∧ R+q^3+q+1≤q^4 ∧ R+1<q^4']:assert f in s,f
n=0
for beta in range(2,9):
 for J in range(1,5):
  q=1+beta*J
  for F in range(1,q):
   for alpha in range(1,q-F):
    for MC,MF in ((0,0),(beta-1,2*beta-1)):
     R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
     assert R>=40 and R+q**3+q+1<=q**4 and R+1<q**4; n+=1

def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
for name in ['ordinary14-87-guard-gap-draft-independent', 'ordinary14-84-rank-lower40-draft-independent']:
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero source interface review; no Lean','finite_controls':n},sort_keys=True,indent=2))
