#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
g=json.loads((D/'research/ordinary14-shifted-guard87-probe/candidate.json').read_bytes())
def calc(v):
 v=v.copy()
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
rng=random.Random(840105)
for _ in range(200):
 v={x:rng.randint(1,5) for x in g['witnesses']};p={x:rng.randint(0,5) for x in g['fixed_numerals']};z=calc(v|p);q=1+v['J']*p['beta'];X=v['X']
 assert z['guard']==(q-v['F']-v['alpha'])*(X+p['K0']*q)-v['F']-v['J']*p['beta']*v['omega']
zeros=0
for q in range(1,9):
 for f in range(1,5):
  for a in range(5):
   for X in range(1,5):
    for K in range(4):
     for b in range(5):
      for h in range(5):
       if (q-f-a)*(X+K*q)==f+b*h:
        zeros+=1;assert f+a<q
assert zeros>0
s=(P/'GuardGap87.lean').read_text()
for t in ('guard_of_zero p v hz','hbeta','hK','(hF : 0<v 1)','(hw : 0<v 6)','ι_lt_ι','mul_nonpos_of_nonpos_of_nonneg'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for n in ('ordinary14-85-guard-rank-draft','ordinary14-aux-graph-norm-client-draft'):
 p=D/'research'/n;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),n
paths=[P/'GuardGap87.lean',D/'research/ordinary14-85-guard-rank-draft/GuardRank85.lean',D/'research/ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean']
print(json.dumps({'scope':'source inventory, finite guard controls and draft receipt replays; no Lean invocation','signed_formula_controls':200,'bounded_guard_zero_cases':zeros,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
