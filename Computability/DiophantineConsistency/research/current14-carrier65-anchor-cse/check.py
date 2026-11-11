#!/usr/bin/env python3
"""One main-norm multiplication shear followed by global modular CSE."""
import gzip,hashlib,json,random,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site: raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
p=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(raw);rows=g['source']; witnesses=g['witnesses'];out=g['output'];edges={r[0]:r for r in rows}
ports={}
for name,meta in g['coefficient_binding']['ports'].items():
 z=(p.parent/'coefficients'/meta['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==meta['gzip_sha256']
 b=gzip.decompress(z);assert hashlib.sha256(b).hexdigest()==meta['raw_sha256'];ports[name]=int.from_bytes(b,'big')
mods=(1000000007,1000000009,998244353); ns=4; rng=random.Random(0xA5C35E)
for p0 in mods: assert all(p0 % n for n in range(2,int(p0**.5)+1))
ps=[p for p in mods for _ in range(ns)]
inputs={v:tuple(rng.randrange(1,p) for p in ps) for v in witnesses}
inputs.update({v:tuple(x%p for p in ps) for v,x in ports.items()})
inputs.update({j:(j,)*len(ps) for j in range(5)})
def ancestors(v):
 seen=set();todo=[v]
 while todo:
  x=todo.pop()
  if x in edges and x not in seen:
   seen.add(x);todo.extend(edges[x][2:])
 return seen
anchor='N1';anc=ancestors(anchor)
# Candidates must lie before aggregation and cannot influence the anchor.
eligible=[r[0] for r in rows[:60] if r[0] not in anc]
def evaluate(rs):
 es={r[0]:r for r in rs}; values=dict(inputs); visited=set();ordered=[]
 def visit(x):
  if x not in es:return
  assert x not in visited or x in values, 'cycle'
  if x in values:return
  visited.add(x); name,op,a,b=es[x];visit(a);visit(b)
  u,v=values[a],values[b]
  values[x]=tuple((i+j if op=='+' else i-j if op=='-' else i*j)%p for i,j,p in zip(u,v,ps));ordered.append(x)
 visit(out)
 # Optimistic global merging of equal fingerprints, including free leaves.
 # Any collisions can only overstate a saving.
 canonical={v:k for k,v in inputs.items()};aliases={};merged=[]
 for x in ordered:
  value=values[x]
  if value in canonical:aliases[x]=canonical[value]
  else:canonical[value]=x;merged.append(x)
 # Recalculate live gates after merging references to identical fingerprints.
 seen=set();todo=[out]
 while todo:
  x=todo.pop();x=aliases.get(x,x)
  if x in es and x not in seen:
   seen.add(x);todo.extend(es[x][2:])
 return {'before':len(ordered),'after':len(seen),'aliases':aliases}
base=evaluate(rows);assert base['before']==65 and base['after']==65
control=[([r[0],r[1],*['duplicate_N0' if x=='N0' else x for x in r[2:]]] if r[0]=='product0' else list(r)) for r in rows]
control.append(['duplicate_N0','+','N0',0])
ctl=evaluate(control);assert ctl['before']==66 and ctl['after']==65 and ctl['aliases'].get('duplicate_N0')=='N0'
results={}
for name in eligible:
 new=[]
 for r in rows:
  new.append([r[0],r[1],*[('anchor_scaled' if x==name else x) for x in r[2:]]])
 new.append(['anchor_scaled','*',name,anchor])
 result=evaluate(new);assert result['before']==66
 results[name]=result
print(json.dumps({'scope':'main-norm t→t*N1, one non-anchor intermediate before final aggregation, optimistic global equal-fingerprint merging', 'graph_sha256':hashlib.sha256(raw).hexdigest(),'moduli':mods,'samples_per_modulus':ns,'seed':0xA5C35E,'positive_control':ctl,'eligible_count':len(eligible),'candidate_below_65':{k:v for k,v in results.items() if v['after']<65},'candidate_below_66':{k:v for k,v in results.items() if v['after']<66},'all':results},sort_keys=True,indent=2))
