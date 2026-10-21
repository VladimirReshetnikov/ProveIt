#!/usr/bin/env python3
"""Regenerate the finite register-value abstraction used by the semantic screen.

Domain: exact naturals0..7 and a single >=8 class. Its transition closure is
checked explicitly. Adapted from the joint research's source_facts.py.
"""
import json,collections,argparse
from pathlib import Path
import inverse_mp as q
ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=q.W/'K219_Construction_2026-10-20/machine/sites219.json');ap.add_argument('--output',type=Path,default=q.W/'source_facts219.json');a=ap.parse_args()
S=json.loads(a.source.read_text());G=q.s.graph_arithmetic(S)[0];assert G==q.s.graph_intervals(S)
C=8;TOP=1<<C;MASK=TOP-1
inc=lambda v:((v&MASK)<<1)|(v&TOP)
dec=lambda v:(v>>1)|(v&TOP)
facts=[[0]*9 for _ in S];seed=[3,0,0,0,3,0,0,0,0];facts[0]=[1<<v for v in seed]
queue=collections.deque([0]);queued={0};updates=0
while queue:
 i=queue.popleft();queued.remove(i);updates+=1
 _,op,arg=S[i]
 for bit,t in enumerate(G[i][1]):
  v=facts[i].copy()
  if op=='CI':v[arg]=inc(v[arg])
  if op=='CD':
   v[arg]=(v[arg]&1)if bit==0 else dec(v[arg]&~1)
   if not v[arg]:continue
  nv=[x|y for x,y in zip(facts[t],v)]
  if nv!=facts[t]:
   facts[t]=nv
   if t not in queued:queue.append(t);queued.add(t)
checks=0;cases=[];excluded=[]
for i,(_,op,arg)in enumerate(S):
 f=facts[i]
 if any(v==0 for v in f):
  excluded.extend([i,b]for b in((False,True)if op=='CD'else(False,)));continue
 for bit,t in enumerate(G[i][1]):
  v=f.copy()
  if op=='CI':v[arg]=inc(v[arg])
  if op=='CD':v[arg]=(v[arg]&1)if bit==0 else dec(v[arg]&~1)
  if op=='CD'and not v[arg]:continue
  assert all(x|y==y for x,y in zip(v,facts[t]));checks+=1
 for bit in((False,True)if op=='CD'else(False,)):
  target=(cases if f[arg]&(~1 if bit else 1)else excluded)if op=='CD'else cases
  target.append([i,bit])
result={'cutoff':C,'facts':facts,'seed':seed,'admitted_cases':cases,'excluded_cases':excluded,'closure_checks':checks,'updates':updates}
a.output.write_text(json.dumps(result,separators=(',',':'))+'\n');print({'sites':len(S),'cases':len(cases),'closure_checks':checks,'updates':updates})
