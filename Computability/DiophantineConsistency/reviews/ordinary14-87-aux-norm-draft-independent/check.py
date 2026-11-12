#!/usr/bin/env python3
"""Independent 87 signed auxiliary norm source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-aux-norm-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','29a69fa9bc408f7f28937f4eea301008637963f4000e3d87a81fe899069e333a')
s=pin(A/'AuxNorm87.lean','ad06a2314ffa96fae3961fa424dc950a854a112761f9c10e5f7e8e17fc183990').decode()
pin(A/'check_source.py','07870609e66d71704211addfc2dce33da5034b5d559440cfb457537f98f20231')
receipt=pin(A/'observation.json','cad565f66b2da42f7bb033bfb9281cb74cd7876c08a8cce68217f88842cef006')
for f in ('(hz : InternalZero (P87ShiftedGuard.graph p).output v)',
 'NaturalRank87Draft.rank_of_87_zero p beta K MC MF v hport hK hMC hMF (hv 1) (hv 6) hz',
 'P72Root.ι_tsub hf2','(FourFields87Draft.fields_of_zero p v hz).2.2.1',
 'P72Aux.ι_absdiff_sq','linear_combination hcore'):
 assert f in s,f
assert 'InternalZero (P86ResidueGraph.graph p).output' not in s
n=0
for z in range(-10,11):
 for u in range(1,9):
  for Q in range(10):
   residual=(z+u)**2-Q*((z+u)**2-z*z)-1
   left=Q*abs(z)**2+abs(z+u)**2
   right=1+Q*abs(z+u)**2
   assert residual==left-right;n+=1
def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
for name in ('ordinary14-87-natural-rank-draft-independent','ordinary14-87-strong-norm-draft-independent'):
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero signed auxiliary norm source review; no Lean','signed_algebra_cases':n},sort_keys=True,indent=2))
