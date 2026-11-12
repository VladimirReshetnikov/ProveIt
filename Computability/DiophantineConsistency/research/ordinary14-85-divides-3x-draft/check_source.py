#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'Divides3X85.lean').read_text()
for t in ('P72ExactIndices85Draft.exact_indices','xx*yy*qq','mul_left_cancel₀','H=3+qq*D','mod_eq_zero_iff_dvd.mp','q beta v∣3*X v'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
count=0;nondiv=0
for q in range(2,10):
 for X in range(1,13):
  if 3*X%q:continue
  for ss in range(1,4):
   Y=q**3*ss;U=Y*q*q;a=X*Y+Y;H=3+4*a;c=7;W=4*X*q*ss;gamma=W;d=X+a*c+H*X//q;R=5;k=R+1+U*W
   assert (H*X)%q==0 and U*d+H*k==U*(X+a*c)+H*(U*gamma+X*Y*q+R+1)
   assert q*(d+H*W)==q*(X+a*c+H*gamma)+H*X and 3*X%q==0
   if X%q:nondiv+=1
   count+=1
assert nondiv>0
p=D/'research/ordinary14-85-p72-exact-indices-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[P/'Divides3X85.lean',p/'P72ExactIndices85.lean',D/'Lean/DiophantineConsistency/Compact44/FreeJPowerProjection.lean']
print(json.dumps({'scope':'source inventory, finite factor-three balance controls and draft receipt replay; no Lean invocation','finite_controls':count,'controls_q_not_dividing_X':nondiv,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
