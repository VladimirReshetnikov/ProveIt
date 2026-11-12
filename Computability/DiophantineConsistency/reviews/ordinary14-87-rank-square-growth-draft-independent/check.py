#!/usr/bin/env python3
"""Independent 87 rank-square growth source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-rank-square-growth-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','9270089315a0c5e37fb283528760fc270cf3189c88390a5912e397abfce0731a')
s=pin(A/'RankSquareGrowth87.lean','8c4bf60dd04a74945916ac3e7533816460170ebf5f79897385835149c9af3d6e').decode()
pin(A/'check_source.py','afa9566053f5e98c32ef8cbe4d5a6945aa1890417d21033de12fd351b5dc26d0')
receipt=pin(A/'observation.json','291ccdb859509d6a27736bd17dd80a5e25de0443c42124f8b372164a84e1155c')
p=D/'reviews/ordinary14-87-power-recovery-draft-independent'
pin(p/'check.py','173ebd700fe355ae8fe62a49fb85c306c78bf9dd88b36749375fc9ee3d8d7d37')
pin(p/'result.json','d3132408f89d7791661457332afb8f7eaeaa2cd17294fded5479480b367f08ad')
for f in ('(hJ : 0<J) (hF : 0<F) (ha : 0<alpha)',
 'have heF : q-F+F=q := tsub_add_cancel_of_le hFq',
 'have he1 : q-1+1=q := tsub_add_cancel_of_le hq1',
 'have hesq : q*q-1+1=q*q := tsub_add_cancel_of_le hq2one',
 'have hsq : q*q≤2*(q*q-1)',
 'PowerRecovery87Draft.power p beta K MC MF v',
 'lt_of_le_of_lt hsq (lt_exp R)'):
 assert f in s,f
n=0
for beta in range(1,10):
 for J in range(1,9):
  q=1+J*beta
  for F in range(1,q):
   for alpha in range(1,q-F):
    G=alpha+(q-F)*(J*beta);R=G*(q*q-1)
    assert G>=5 and q*q<=2*(q*q-1)<=R
    assert R.bit_length()<=R;n+=1
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not r.stderr and r.stdout==receipt
print(json.dumps({'scope':'scalar rank-square and conditional power source review; no Lean',
 'finite_scalar_controls':n,'prior_power_review':'pinned, not rerun'},sort_keys=True,indent=2))
