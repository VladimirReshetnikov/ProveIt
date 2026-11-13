#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'P72FirstInputs85.lean').read_text()
for t in ('rank_window','first_index_mod_q4','mod_eq_self_of_lt hlt','26≤R','(2*n)%(q^4)=R+1'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
rng=random.Random(840113);count=0
while count<300:
 q=rng.randint(3,20);R=rng.randint(40,q**4-2) if q**4>=42 else 40
 if R+1>=q**4:continue
 t=rng.randint(0,6);x=R+1+t*q**4
 if x%2:continue
 n=x//2;assert 26<=R and R+1<q**4 and (2*n)%q**4==R+1;count+=1
for name in ('ordinary14-85-first-index-modq4-draft','ordinary14-85-rank-window-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'P72FirstInputs85.lean',D/'research/ordinary14-85-first-index-modq4-draft/FirstIndexModQ485.lean',D/'research/ordinary14-85-rank-window-draft/RankWindow85.lean']
print(json.dumps({'scope':'source inventory, finite modulo/window controls and two draft receipt replays; no Lean invocation','finite_controls':count,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
