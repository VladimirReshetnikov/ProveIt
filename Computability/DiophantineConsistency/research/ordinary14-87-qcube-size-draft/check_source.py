from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'QCubeSize87.lean').read_text()
for t in ('FirstQuotient87Draft.quotient_and_root','QCubeSize84Draft.Y_at_least_eight','Function.update v 7 s','P87ShiftedGuard.graph p'):assert t in s
for name in ('ordinary14-87-first-quotient-draft','ordinary14-84-qcube-size-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for b in range(1,15):
 for J in range(1,15):
  q=1+b*J
  for s in range(1,15):
   assert q**3*s>=8
   count+=1
print(json.dumps({'size_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'QCubeSize87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
