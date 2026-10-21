#!/usr/bin/env python3
"""Source-only reconstruction, exact CFG checks and finite corroboration. No TM claim."""
from pathlib import Path
from math import isqrt
import json,hashlib
import source_language as s
R=Path(__file__).resolve().parent
old=json.loads((R/'parent.sites.json').read_text());root=s.tree(old)
body=s.subtree(root,'111');clear,copy=body[0];nip=body[1]
assert len(s.sites(clear))==2 and len(s.sites(copy))==7 and len(s.sites(nip))==26
assert s.subtree(nip,'10000') == (('CD',5),((('CD',6),('CC',2)),('CB',1)))
assert s.subtree(nip,'10010') == (('CD',5),('CC',1))
newnip=s.replace(nip,'10000',(('CD',5),(('CI',1),((('CD',6),('CC',3)),('CB',1)))))
newnip=s.replace(newnip,'10010',(('CD',5),(('CI',1),('CC',2))))
newbody=clear,newnip
newroot=s.replace(root,'111',newbody);new=s.sites(newroot)
raw=s.compact(new);path=R/'fused30.sites.json'
if path.exists():assert path.read_bytes()==raw
else:path.write_bytes(raw)
graph,count=s.graph_arithmetic(new)
assert graph==s.graph_intervals(new)
assert s.boundary(newroot)==(0,0,True)
assert s.metrics(newroot)=={'dag_nodes':208,'leaf_occurrences':4727,'maximum_depth':44,'maximum_zero_run':6}
assert len(s.sites(newbody))==30 and count==6144
assert new[4703][1:]==['CC',3] and graph[4703]==[['identity'],[4700]]
assert graph[4708]==[['identity'],[4706]]
assert all(t==0 or 4697<=t<4727 for g in graph[4697:]for t in g[1])
oldgraph=s.graph_intervals(old)
assert graph[:4697]==oldgraph[:4697]

def run(regs):
 pc=4697;steps=0
 while pc:
  assert 4697<=pc<4727
  effect,targets=graph[pc];op=effect[0]
  if op=='halt':return None,steps
  if op=='increment':regs[effect[1]]+=1;pc=targets[0]
  elif op=='decrement':
   r=effect[1];positive=regs[r]>0;regs[r]-=int(positive);pc=targets[int(positive)]
  else:assert op=='identity';pc=targets[0]
  steps+=1;assert steps<100000
 return regs,steps
trials=maxsteps=0
for top in range(6):
 for w in range(100):
  ss=(isqrt(8*w+1)-1)//2;y=w-ss*(ss+1)//2;x=ss-y
  for d in (0,3,12):
   for h in range(8):
    ans,steps=run([19,top,w,17,d,h,0,0,23]);maxsteps=max(maxsteps,steps)
    assert (ans is None) if h==1 else ans==[19,h,y,17,d,x,0,0,23]
    trials+=1
result={'status':'SOURCE_RECONSTRUCTION_AND_FINITE_CORROBORATION_PASS','parent_sha256':hashlib.sha256((R/'parent.sites.json').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(raw).hexdigest(),'metrics':s.metrics(newroot),'guarded_cases':count,'body_leaves':30,'comparison_continue':{'ordinal':4703,'opcode':'CC3','target':4700},'finite_trials':trials,'max_primitive_steps':maxsteps,'scope':'Exact source reconstruction and finite corroboration only; all-natural source proof is in FUSED30_NOTE.md. No binary table or state count claimed.'}
(R/'check.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
