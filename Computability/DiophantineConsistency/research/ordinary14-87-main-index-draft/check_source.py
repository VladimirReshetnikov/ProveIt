from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'MainIndex87.lean').read_text()
for t in ('QCubeSize87Draft.Y_at_least_eight','MainBalance87Draft.norm_and_balance','ArithmeticPellClassification.solution_index','P87ShiftedGuard.graph p','X v*Y v*q beta v'):assert t in s
for name in ('ordinary14-87-qcube-size-draft','ordinary14-87-main-balance-conditional-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for a in range(1,20):
 delta=(a+1)*(a+3);assert delta==3+4*a+a*a
 x,y=1,0
 for n in range(1,8):
  x,y=(a+2)*x+delta*y,x+(a+2)*y
  assert x*x==1+delta*y*y
  count+=1
print(json.dumps({'pell_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'MainIndex87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
