"""Fresh finite abstract-induction proof of K219 NOP-source equivalence.
Each primary register is zero or positive; joins are pointwise unions.
"""
from pathlib import Path
from collections import deque
import json,sys,hashlib
from environment import BASE_SOURCE, PACKET, s
import argparse
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--source',type=Path,default=PACKET/'machines/nop219/sites.json');ap.add_argument('--out',type=Path,required=True);args=ap.parse_args();ROOT=args.out;ROOT.mkdir(parents=True,exist_ok=True)
old=json.loads(BASE_SOURCE.read_text());new=json.loads(args.source.read_text())
gs=[]
for rows in(old,new):
 g=s.graph_intervals(rows);assert s.graph_arithmetic(rows)[0]==g;gs.append(g)
oldg,g=gs;cut=4597;end=4603
assert[len(old),len(new)]==[4744,4750]
assert [x[1:]for x in old]==[x[1:]for x in new[:cut]+new[end:]]
assert [x[1:]for x in new[cut:end]]==[['CD',7],['CI',6],['CC',2],['CD',4],['CI',5],['CC',2]]
seed=[3,0,0,0,3,0,0,0,0];facts=[None]*len(new);facts[0]=tuple(1 if x==0 else 2 for x in seed);todo=deque([0]);count=0
while todo:
 i=todo.popleft();v=facts[i];count+=1;op,a=new[i][1:];succ=g[i][1];posts=[]
 if op=='CH':continue
 if op=='CI':
  u=list(v);u[a]=2;posts=[(succ[0],tuple(u))]
 elif op=='CD':
  if v[a]&1:u=list(v);u[a]=1;posts.append((succ[0],tuple(u)))
  if v[a]&2:u=list(v);u[a]=3;posts.append((succ[1],tuple(u)))
 else:posts=[(succ[0],v)]
 for j,u in posts:
  w=u if facts[j]is None else tuple(a|b for a,b in zip(u,facts[j]))
  if w!=facts[j]:facts[j]=w;todo.append(j)
assert facts[cut][4]==facts[cut][7]==1
assert facts[4600][4]==facts[4600][7]==1
assert facts[4598]is None and facts[4599]is None and facts[4601]is None and facts[4602]is None
# This normalizer follows only the two admitted zero decrements in the inserted NOP.
def norm(i):
 seen=set()
 while cut<=i<end:
  assert i not in seen;seen.add(i)
  assert i in(cut,cut+3)and new[i][1]=='CD'and facts[i][new[i][2]]==1
  i=g[i][1][0]
 return i if i<cut else i-6
matches=0
for i,(ef,succ)in enumerate(oldg):
 j=i if i<cut else i+6;nef,nsucc=g[j]
 assert ef==nef and succ==list(map(norm,nsucc)),(i,j,succ,nsucc)
 matches+=len(succ)
rec={'status':'FRESH_ZERO_INVARIANT_AND_NOP_STUTTERING_SOURCE_PASS','old_sites':len(old),'new_sites':len(new),'inserted_interval':[cut,end],'inserted_admitted_path':[4597,4600],'required_zero_registers':[4,7],'abstract_values_at_entry':facts[cut],'abstract_fixpoint_work_items':count,'all_outside_source_successors_checked':matches,'source_metrics':s.metrics(s.tree(new)),'scope':'Pointwise zero/positive abstract interpretation is an inductive overapproximation from the exact seed. The inserted six-leaf transfer block executes only two zero decrement guards, changes no registers, and exits; contracting it yields the old complete guarded CFG. This is an ordinary finite induction certificate, not a proof-assistant endpoint.'}
(ROOT/'source_equivalence.json').write_text(json.dumps(rec,indent=2)+'\n');(ROOT/'zero_facts.json').write_text(json.dumps(facts,separators=(',',':'))+'\n');print(json.dumps(rec,indent=2))
