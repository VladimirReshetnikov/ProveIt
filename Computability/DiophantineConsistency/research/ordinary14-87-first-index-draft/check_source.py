from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'FirstIndex87.lean').read_text()
for t in ('FirstQuotient87Draft.quotient_and_root','ArithmeticPellFirstNorm.solution_residues','(v 6*v 7)*v 7','P87ShiftedGuard.graph p','n≤k v'):assert t in s
r=D/'research/ordinary14-87-first-quotient-draft';x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for m in range(1,9):
 A=2*m-1; d=(A+1)*(A+3); x,y=1,0
 for n in range(1,8):
  x,y=(A+2)*x+d*y,x+(A+2)*y
  K=2*y
  assert x*x==1+m*(m+1)*K*K
  assert (x-1)%(2*m)==0 and (K-2*n)%(4*m)==0
  count+=1
print(json.dumps({'pell_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'FirstIndex87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
