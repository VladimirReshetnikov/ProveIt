from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'Growth87.lean').read_text()
for t in ('Divides3X87Draft.divides_three_X','P72ExactIndices87Draft.exact_indices','power_bound xx yy','hbeta46 : 46≤beta','P87ShiftedGuard.graph p'):assert t in s
r=D/'research/ordinary14-87-divides-3x-draft';x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for beta in range(46,80):
 for J in range(1,9):
  q=beta*J+1
  for X in range(1,40):
   if 3*X%q==0:
    assert X>=16
    count+=1
print(json.dumps({'threshold_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'Growth87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
