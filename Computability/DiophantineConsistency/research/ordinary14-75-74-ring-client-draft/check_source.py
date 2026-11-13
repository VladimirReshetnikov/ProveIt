#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1]
def load(name):return json.loads((D/'research'/name/'candidate.json').read_bytes())
a=load('ordinary14-negative-pell75');b=load('ordinary14-positive-guard74')
assert len(a['source'])==75 and len(b['source'])==74
assert a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']
def calc(g,v):
 v=v.copy()
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
rng=random.Random(7574)
for _ in range(500):
 v={x:rng.randrange(-6,7) for x in a['witnesses']+a['fixed_numerals']}
 x=calc(a,v);w=v.copy();w['h']+=1;y=calc(b,w)
 assert all(x[k]==y[k] for k in ('F0','F1','Fa','Fs'))
 assert x['Fg']==y['guard'] and x['out']==y['out']
for name in ('P75NegativePell','P74PositiveGuard'):
 assert (D/'research/ordinary14-unit75-guard74-lean-draft'/(name+'.lean')).exists()
p=D/'research/ordinary14-unit75-guard74-lean-draft'
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'make_graph.py'),'--check'],cwd=D,capture_output=True,check=True,timeout=90)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[P/'Ring75To74.lean',p/'P75NegativePell.lean',p/'P74PositiveGuard.lean']
print(json.dumps({'scope':'literal graph receipt, ring-cut source and finite signed controls; no Lean','signed_controls':500,'files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
