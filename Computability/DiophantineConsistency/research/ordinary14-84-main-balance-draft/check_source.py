#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
s=(H/'MainBalance.lean').read_text()
for x in ('oriented_main_root','ι_injective','(hY : 8≤','(hR : AuxGraphNormClientDraft.rank','U*d+H*AuxGraphNormClientDraft.k v','hroot'):assert x in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
rng=random.Random(840104)
for _ in range(200):
 q=rng.randint(2,8);w=rng.randint(1,5);Y=q**3*rng.randint(1,3);U=Y*q*q;X=q*w;eta=rng.randint(1,5);k=eta+rng.randint(1,5);R=k-1;gamma=rng.randint(1,5);a=X*Y+Y;c=eta+Y*k;hh=3+4*a
 d=X+a*c+hh*gamma;main=U*(X+a*c)+hh*(U*gamma-(k-R-1))
 assert main==U*d and U*d+hh*k==U*(X+a*c)+hh*(U*gamma+R+1)
p=D/'research/ordinary14-84-main-orientation-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[H/'MainBalance.lean',p/'MainOrientation.lean']
print(json.dumps({'scope':'source/interface inventory, finite algebra controls and dependency replay only; no Lean invocation','finite_controls':200,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
