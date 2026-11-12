#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
g=json.loads((D/'research/ordinary14-qcube85-tradeoff/candidate.json').read_bytes())
def calc(v):
 v=v.copy()
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
rng=random.Random(850103)
for _ in range(300):
 v={x:rng.randint(1,6) for x in g['witnesses']};p={x:rng.randint(1,6) for x in g['fixed_numerals']};q=1+v['J']*p['beta'];v['F']=rng.randint(1,q);z=calc(v|p)
 X=v['X'];Y=q**3*v['s'];U=Y*q*q;k=v['eta']+v['zeta'];a=X*Y+Y;c=v['eta']+Y*k;delta=3+4*a+a*a;H=3+4*a;R=z['R']
 main=U*(X+a*c)+H*(U*v['gamma']+X*Y*q-(k-R-1))
 assert Y>=8 and R>=0 and main>0
 assert z['A1']==main*main-U*U*(1+delta*c*c)
 assert main+H*k==U*(X+a*c)+H*(U*v['gamma']+X*Y*q+R+1)
s=(P/'MainBalance85.lean').read_text()
for t in ('fields85 p v hz','rank_of_85_zero','main_parts_positive','scaled_signed_root','ι_injective','X v*Y beta v*q beta v','(hv 7)'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-85-direct-norms-draft','ordinary14-84-qcube-size-draft','ordinary14-scaled-signed-root-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'MainBalance85.lean',D/'research/ordinary14-85-direct-norms-draft/DirectNorms85.lean',D/'research/ordinary14-85-guard-rank-draft/GuardRank85.lean',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveMainOrientation2011.lean']
print(json.dumps({'scope':'source inventory, finite literal main-field controls and draft receipt replays; no Lean invocation','finite_controls':300,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
