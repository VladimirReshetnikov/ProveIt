#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,math,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'Q4Rank85.lean').read_text()
for t in ('MainBalance85Draft.norm_and_balance','q4_rank_from_balance','xx*yy*qq+(R+1)','uu=qq^5*v 7','(P85QcubeGraph.graph p).output v'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
count=0;nondiv=0
for q in range(2,12):
 for X in range(1,6):
  for ss in range(1,4):
   Y=q**3*ss;U=Y*q*q;H=3+4*Y*(X+1);g=math.gcd(U,H);step=U//g;t=(X*Y*q+step)//step;k=5;R=k-1-X*Y*q+step*t;A=11;gamma=2;d=A+H*gamma+(H//g)*t
   assert R>=0 and U*d+H*k==U*A+H*(U*gamma+X*Y*q+R+1)
   assert abs(R+1-k)%q**4==0
   if X%q:nondiv+=1
   count+=1
for name in ('ordinary14-85-main-balance-draft','ordinary14-shifted-guard87-fact-lemmas-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr
 if name=='ordinary14-shifted-guard87-fact-lemmas-draft':
  obj=json.loads(r.stdout); key=str((p/'ShiftedGuardFacts.lean').relative_to(D)); assert obj['sha256'][key]==hashlib.sha256((p/'ShiftedGuardFacts.lean').read_bytes()).hexdigest()
 else: assert r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'Q4Rank85.lean',D/'research/ordinary14-85-main-balance-draft/MainBalance85.lean',D/'research/ordinary14-shifted-guard87-fact-lemmas-draft/ShiftedGuardFacts.lean']
print(json.dumps({'scope':'source inventory, finite old-carrier balances and draft receipt replays; no Lean invocation','finite_controls':count,'controls_q_not_dividing_X':nondiv,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
