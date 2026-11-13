#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'RankWindow85.lean').read_text()
for t in ('gap_of_85_zero','scalar_rank_window','(hMC : MC<beta)','(hMF : MF<2*beta)','R+1<q^4','40≤R'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
rng=random.Random(840111);count=0
while count<500:
 beta=rng.randint(1,10);J=rng.randint(1,10);q=1+J*beta
 if q<3:continue
 F=rng.randint(1,q-2);alpha=rng.randint(1,q-F-1);MC=rng.randrange(beta);MF=rng.randrange(2*beta)
 R=(alpha+(q-F)*J*beta)*(q*q-1)+J*(MC+MF*q)
 assert R==((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
 assert 40<=R and R+q**3+q+1<=q**4 and R+1<q**4;count+=1
p=D/'research/ordinary14-85-guard-rank-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
lo=D/'research/ordinary14-84-rank-lower40-draft';t=subprocess.run([sys.executable,'-I','-S','-B',str(lo/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not t.stderr and t.stdout==(lo/'observation.json').read_bytes()
paths=[P/'RankWindow85.lean',p/'GuardRank85.lean',lo/'RankLower40.lean',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean']
print(json.dumps({'scope':'source inventory, finite scalar window controls and natural-rank receipt replay; no Lean invocation','finite_controls':count,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
