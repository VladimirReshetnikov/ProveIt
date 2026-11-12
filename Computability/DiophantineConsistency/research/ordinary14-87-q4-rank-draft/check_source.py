from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'Q4Rank87.lean').read_text()
for t in ('FirstQuotient87Draft.quotient_and_root','QCubeSize87Draft.Y_at_least_eight','MainBalance87Draft.norm_and_balance','q4_rank_from_balance','s*(xx+aa*cc+H*v 12)','P87ShiftedGuard.graph p'):assert t in s
for name in ('ordinary14-87-first-quotient-draft','ordinary14-87-qcube-size-draft','ordinary14-87-main-balance-conditional-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for q in range(2,10):
 for X in range(1,10):
  for s0 in range(1,5):
   Y=q**3*s0;H=3+4*Y*(X+1)
   for n in range(1,20):
    if H*n%q**5==0:
     assert n%q**4==0
    count+=1
print(json.dumps({'factor_three_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'Q4Rank87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
