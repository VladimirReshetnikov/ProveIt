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
rng=random.Random(850101)
for _ in range(300):
 v={x:rng.randint(1,6) for x in g['witnesses']};p={x:rng.randint(0,6) for x in g['fixed_numerals']};q=1+v['J']*p['beta'];v['F']=rng.randint(0,q);z=calc(v|p)
 assert z['guard']==(q-v['F']-v['alpha'])*(v['X']+p['K0'])-v['F']-v['J']*p['beta']*v['h']
 assert z['R']==(v['alpha']+(q-v['F'])*v['J']*p['beta'])*(q*q-1)+v['J']*(p['MC']+p['MF']*q)
s=(P/'GuardRank85.lean').read_text()
for t in ('P85QcubeGraph.graph p','fields85 p v hz','let X := v 6','gap_of_85_zero','NaturalRank84Draft.rank_repr','hMC','hMF'):assert t in s
assert 'fields84' not in s and 'AuxGraphNormClientDraft.X' not in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-84-guard-gap-draft','ordinary14-84-natural-rank-draft','ordinary14-qcube85-lean-draft'):
 p=D/'research'/name;script='make_graph.py' if name.endswith('lean-draft') else 'check_source.py';args=[sys.executable,'-I','-S','-B',str(p/script)]
 if script=='make_graph.py':args.append('--check')
 r=subprocess.run(args,cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'GuardRank85.lean',D/'research/ordinary14-84-natural-rank-draft/NaturalRank.lean',D/'research/ordinary14-qcube85-lean-draft/P85QcubeGraph.lean']
print(json.dumps({'scope':'source inventory, finite literal guard/rank controls and draft receipt replay; no Lean invocation','finite_controls':300,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
