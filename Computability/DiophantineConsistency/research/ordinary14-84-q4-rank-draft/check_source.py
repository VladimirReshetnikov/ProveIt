#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,math,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'Q4Rank.lean').read_text()
for t in ('PositiveMainBalance84Draft.norm_and_balance','q4_from_modified_balance','q^3∣Y','U=q^5*v 7','magnitude (R+1,AuxGraphNormClientDraft.k v)'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
n=0;sharp=0
for q in range(2,13):
 for w in range(1,4):
  for ss in range(1,4):
   X=q*w;Y=q**3*ss;U=Y*q*q;H=3+4*Y*(X+1);g=math.gcd(U,H);k=5;R=k-1+U//g;A=11;gamma=2;d=A+H*gamma+H//g
   assert U*d+H*k==U*A+H*(U*gamma+R+1)
   assert abs((R+1)-k)%q**4==0
   if q==3 and ss==1: assert abs(R+1-k)==q**4;sharp+=1
   n+=1
for name in ('ordinary14-84-positive-main-balance-draft','ordinary14-modified-carrier-model-facts-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'Q4Rank.lean',D/'research/ordinary14-84-positive-main-balance-draft/PositiveMainBalance.lean',D/'research/ordinary14-modified-carrier-model-facts-draft/ModifiedCarrierFacts.lean']
print(json.dumps({'scope':'source inventory, finite balance/factor-three controls and dependency receipt replays; no Lean invocation','finite_controls':n,'q3_sharp_controls':sharp,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
