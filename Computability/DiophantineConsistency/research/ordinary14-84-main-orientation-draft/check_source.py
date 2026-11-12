#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
s=(H/'MainOrientation.lean').read_text()
for x in ('modified_main_parts_positive','signed_main_root','ι_lt_ι','neg_nonpos.mpr','(hY : 8≤','(hR : AuxGraphNormClientDraft.rank'):assert x in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
rng=random.Random(840103)
for _ in range(300):
 q=rng.randint(2,10); w=rng.randint(1,6); ss=rng.randint(1,4); Y=q**3*ss; U=Y*q*q; X=q*w
 eta=rng.randint(1,5);zeta=rng.randint(1,5);k=eta+zeta; R=rng.randint(0,20);gamma=rng.randint(1,5)
 a=X*Y+Y;c=eta+Y*k;hh=3+4*a; L=U*(X+a*c)+hh*(U*gamma+R+1);N=hh*k
 assert Y>=8 and U>0 and k>0 and N<L
 assert L-N==U*(X+a*c)+hh*(U*gamma-(k-R-1))
for name in ('ordinary14-84-signed-main-norm-draft','ordinary14-modified-carrier-model-facts-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[H/'MainOrientation.lean',D/'research/ordinary14-84-signed-main-norm-draft/SignedMainNorm.lean',D/'research/ordinary14-modified-carrier-model-facts-draft/ModifiedCarrierFacts.lean']
print(json.dumps({'scope':'source inventory, finite natural-inequality controls and dependency replays only; no Lean invocation','finite_controls':300,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
