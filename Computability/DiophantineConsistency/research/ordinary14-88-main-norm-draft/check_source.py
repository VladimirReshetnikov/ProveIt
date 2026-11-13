from pathlib import Path
import hashlib,json,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'MainNorm88.lean').read_text()
for t in ('FirstQuotient88Draft.forward_zero','FourFields87Draft.fields_of_zero','MainBalance87Draft.main_eval','root_of_scaled_ring_square','P88QuotientGuarded.graph p','hY : 0<v 7'):assert t in s
for name in ('ordinary14-88-first-quotient-draft','ordinary14-87-main-balance-conditional-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for U in range(1,9):
 for d in range(10):
  for sign in (-1,1):
   z=sign*U*d
   assert z*z==U*U*(d*d)
   count+=1
print(json.dumps({'signed_scale_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'MainNorm88.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
