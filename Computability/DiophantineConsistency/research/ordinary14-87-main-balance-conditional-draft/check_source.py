from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'MainBalance87.lean').read_text()
for t in ('hY8 : 8≤Y v','FourFields87Draft.fields_of_zero','NaturalRank87Draft.rank_of_87_zero','main_parts_positive','scaled_signed_root','X v*Y v*q beta v','P87ShiftedGuard.graph p'):assert t in s
for name in ('ordinary14-87-four-fields-draft','ordinary14-87-natural-rank-draft','ordinary14-87-strong-norm-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for X in range(1,8):
 for Y in range(8,15):
  for q in range(1,6):
   for k in range(1,6):
    eta=1;c=eta+Y*k;a=X*Y+Y;U=Y*q*q;H=3+4*a
    assert H*k < U*(X+a*c)+H*(X*Y*q+1)
    count+=1
print(json.dumps({'orientation_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'MainBalance87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
