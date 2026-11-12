from pathlib import Path
import json,hashlib,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'RankSquareGrowth87.lean').read_text()
for t in ('scalar_rank_square','tsub_add_cancel_of_le hq2one','mul_le_mul_of_nonneg_right hG2','GuardGap87Draft.gap_of_87_zero','PowerRecovery87Draft.power','lt_exp R','P87ShiftedGuard.graph p'):assert t in s
for name in ('ordinary14-87-power-recovery-draft','ordinary14-87-guard-gap-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for beta in range(1,13):
 for J in range(1,7):
  q=1+J*beta
  for F in range(1,q):
   for a in range(1,q-F):
    G=a+(q-F)*J*beta;R=G*(q*q-1)
    assert R>=q*q
    count+=1
print(json.dumps({'scalar_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'RankSquareGrowth87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
