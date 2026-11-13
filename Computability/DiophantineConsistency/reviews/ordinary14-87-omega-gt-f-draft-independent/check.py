#!/usr/bin/env python3
"""Independent 87 own-zero omega>F source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-omega-gt-f-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'OmegaGtF87.lean','4ee875a128c462aef63f29e4750ab0bf52aab57508c68790bd0878858f73583c').decode()
pin(A/'check_source.py','b2e0147fc2566ac706b41eb4c62b77a1437beeddacb186cc370a7d0ae9d73389')
receipt=pin(A/'observation.json','8f1bd2c4d410e6580eef48d237d3422aa0413e74f0596875fd93c05756da5639')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-87-omega-gt-f-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='fb9243e8ad404629563b7189b5c92d328b52f59025e98da6eb887032110c8578'
p=D/'reviews/ordinary14-87-rank-square-growth-draft-independent'
pin(p/'check.py','e05f4882929e7ebe7f929d80fad25a1861bde385122fc7b1d00bc692badf0e05')
pin(p/'result.json','a3ff36da7a2c546e2028248783dd76db2917b26e9b9807c14c13c7f465019621')
for f in ('(hz : InternalZero (P87ShiftedGuard.graph p).output v)',
 'GuardGap87Draft.gap_of_87_zero p beta K v hport hK (hv 1) (hv 6) hz',
 'RankSquareGrowth87Draft.X_gt_q_square p beta K MC MF v',
 'have hqF : qq*(v 1)<qq*qq','have hCcast : ι cc=ι qq-ι (v 1)-ι (v 2)',
 'have hnat : bb*v 13+v 1=cc*(v 6+K*qq)',
 'exact (mul_lt_mul_left hb).mp hmul'):
 assert f in s,f
n=0
for q in range(3,20):
 b=q-1
 for F in range(1,q):
  for alpha in range(1,q-F):
   C=q-F-alpha
   for K in range(4):
    for X in (q*q+1,q*q+2,q*q+3,q*q+q):
     z=C*(X+K*q)-F
     if z%b:continue
     omega=z//b
     assert q*F<q*q<X<=C*(X+K*q)
     assert b*omega+F==C*(X+K*q) and F<omega;n+=1
assert n>0
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'87 own-zero omega>F source review; no Lean','finite_guard_cases':n,'prior_growth_review':'pinned, not rerun'},sort_keys=True,indent=2))
