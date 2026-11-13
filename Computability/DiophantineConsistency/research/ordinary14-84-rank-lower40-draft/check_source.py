#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'RankLower40.lean').read_text()
for t in ('scalar_lower40','rank_lower40','hgap1 : F+alpha+1≤q','tsub_add_cancel_of_le hFq','tsub_add_cancel_of_le hq1','gap_of_84_zero','40≤naturalRank'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
rng=random.Random(840112);count=0
while count<1000:
 beta=rng.randint(1,20);J=rng.randint(1,8);q=1+J*beta
 if q<3:continue
 F=rng.randint(1,q-2);alpha=rng.randint(1,q-F-1);MC=rng.randint(0,40);MF=rng.randint(0,40)
 R=(alpha+(q-F)*J*beta)*(q*q-1)+J*(MC+MF*q)
 assert q>=3 and q-F>=2 and q-1>=2 and (alpha+(q-F)*J*beta)>=5 and q*q-1>=8 and R>=40;count+=1
beta=2;J=1;q=3;F=alpha=w=h=1;K=MC=MF=0;X=q*w;R=(alpha+(q-F)*J*beta)*(q*q-1)
assert (q-F-alpha)*(X+K)-F-J*beta*h==0 and R==40
p=D/'research/ordinary14-84-natural-rank-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[P/'RankLower40.lean',p/'NaturalRank.lean']
print(json.dumps({'scope':'source inventory, finite scalar controls and natural-rank receipt replay; no Lean invocation','finite_controls':count,'sharp_guard_partial':True,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
