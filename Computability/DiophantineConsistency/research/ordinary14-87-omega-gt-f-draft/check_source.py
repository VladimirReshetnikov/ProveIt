from pathlib import Path
import json,hashlib,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'OmegaGtF87.lean').read_text()
for t in ('RankSquareGrowth87Draft.X_gt_q_square','GuardGap87Draft.guard_of_zero','cast_C beta v hgap','mul_lt_mul_of_pos_left hF hq','mul_lt_mul_left hb','P87ShiftedGuard.graph p'):assert t in s
for name in ('ordinary14-87-rank-square-growth-draft','ordinary14-87-guard-gap-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for b in range(2,15):
 q=b+1
 for F in range(1,q):
  for alpha in range(1,q-F):
   C=q-F-alpha
   for X in range(q*q+1,q*q+5):
    for K in range(8):
     num=C*(X+K*q)-F
     if num%b==0:
      omega=num//b
      assert F<omega
      count+=1
print(json.dumps({'positive_guard_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'OmegaGtF87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
