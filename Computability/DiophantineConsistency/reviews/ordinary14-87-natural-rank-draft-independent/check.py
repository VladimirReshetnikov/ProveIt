#!/usr/bin/env python3
"""Independent 87 own-zero natural-rank source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-natural-rank-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','343bf4ca5a6c023108a74818afc73e7b200ba5c4ea48a68bd1907ba526d242ac')
s=pin(A/'NaturalRank87.lean','11910887d1eca08881a664b183fddf588f434165281f2f6b1edd5620afa4c7bf').decode()
pin(A/'check_source.py','6702a0def6cbedae8c08cc53fe98059768f10d5048876e4dc53edb426afd1818')
receipt=pin(A/'observation.json','1e74333e43b8ae00e08638648f7fbce5ed99dc66efb2f3b7dcd7ff5df725f171')
for f in ('(hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)',
 '(hMC : (p 2 : DiffRing V)=ι MC) (hMF : (p 3 : DiffRing V)=ι MF)',
 '(hz : InternalZero (P87ShiftedGuard.graph p).output v)',
 'GuardGap87Draft.gap_of_87_zero p beta K v hbeta hK hFpos hX hz',
 'NaturalRank84Draft.rank_repr p beta MC MF v hMC hMF hF hq2'):
 assert f in s,f
assert 'InternalZero (P86ResidueGraph.graph p).output' not in s
n=0
for q in range(1,25):
 for F in range(q+1):
  assert max(q-F,0)==q-F and max(q*q-1,0)==q*q-1;n+=1
def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-87-guard-gap-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero natural-rank source review; no Lean','bounded_subtraction_cases':n},sort_keys=True,indent=2))
