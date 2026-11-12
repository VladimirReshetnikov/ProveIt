from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'Divides3X87.lean').read_text()
for t in ('P72ExactIndices87Draft.exact_indices','FirstQuotient87Draft.quotient_and_root','4*xx*qq*s0*s','4*(qq*qq)*s0*(xx+1)','mul_left_cancel₀','P87ShiftedGuard.graph p'):assert t in s
for name in ('ordinary14-87-p72-exact-indices-draft','ordinary14-87-first-quotient-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for q in range(2,12):
 for X in range(1,10):
  for s0 in range(1,6):
   Y=q**3*s0;U=Y*q*q;H=3+4*Y*(X+1);D0=4*q*q*s0*(X+1)
   for w in range(5):
    W=4*X*q*s0*w
    assert U*W==4*X*Y*Y*w and H==3+q*D0
    count+=1
print(json.dumps({'projection_identity_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'Divides3X87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
