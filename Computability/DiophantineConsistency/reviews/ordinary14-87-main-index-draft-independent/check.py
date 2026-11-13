#!/usr/bin/env python3
"""Independent 87 source interface review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-main-index-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','daf819d1e2912c3280ac2a84ea70ab1ee97c04a3f4b793cf3a2c91a07ebcf87c')
s=pin(A/'MainIndex87.lean','10da72dfb53dd040258b35d4dfb147bbcddc32d7f4bb21e80948a65335a42326').decode()
pin(A/'check_source.py','50cddd666a5ff98fdc9f2aec0abf2625660eb295020f71250e89db1e08368a5a')
receipt=pin(A/'observation.json','03158dc7a91f495e4e323678da34ab1b193f3e6904a7b15259801e556ee5469f')
for f in ['QCubeSize87Draft.Y_at_least_eight p beta v hbeta (hv 0) (hv 7) hport hz', 'MainBalance87Draft.norm_and_balance p beta K MC MF v', 'ArithmeticPellClassification.solution_index (a v) d (c v) hnorm', 'xcoord m (a v)=d ∧ ycoord m (a v)=c v', 'H*(U beta v*v 12+X v*Y v*q beta v+R+1)']:assert f in s,f
n=0
for a in range(1,12):
 p=a+2;delta=p*p-1;x,y=1,0
 for j in range(1,9):
  x,y=p*x+delta*y,x+p*y
  assert x*x==1+(a*a+4*a+3)*y*y;n+=1

def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
for name in ['ordinary14-87-main-balance-conditional-draft-independent', 'ordinary14-87-qcube-size-draft-independent']:
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero source interface review; no Lean','finite_controls':n},sort_keys=True,indent=2))
