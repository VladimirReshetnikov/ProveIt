from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1]
s=(p/'StrongNorm87.lean').read_text()
for t in ('FourFields87Draft.fields_of_zero p v hz','strong_norm_of_ring_residual','v 6*v 7+v 7','v 9+v 7*k v'):assert t in s
r=D/'research/ordinary14-87-four-fields-draft'
x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for X in range(4):
 for Y in range(4):
  for eta in range(1,4):
   for zeta in range(1,4):
    a=X*Y+Y;c=eta+Y*(eta+zeta);d=3+4*a+a*a
    for i in range(3):
     for f in range(3):
      z=(i*c*c)**2-d*(f*f-1)
      assert (z==0)==((i*c*c)**2+d==d*f*f)
      count+=1
print(json.dumps({'controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'StrongNorm87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
