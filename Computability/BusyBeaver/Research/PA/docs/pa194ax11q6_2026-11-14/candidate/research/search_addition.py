#!/usr/bin/env python3
"""Enumerate short shared increment-body DAGs; test conservative local folds."""
from pathlib import Path
import sys, json, itertools, time, collections
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sys.path.insert(0,str(ROOT));import build_ax11q6 as x
c,b=x.c,x.b
c.machine=lambda:(dict(x.BASE),[])
g=c.read_grammar(ROOT/'inputs/grammar.json')
base,index,shape=c.build(g)
base[164,1]=(1,True,114)
best=10000;records=[];total=0;started=time.monotonic()
def visit(helpers, counts, defs, hmax):
 global best,total
 choices=[61,99]+helpers
 if helpers:
  roots=[z for z in itertools.product(choices,repeat=2)if helpers[-1] in z]
 else: roots=list(itertools.product(choices,repeat=2))
 for left,right in roots:
  k=counts[left]+counts[right]
  if k<4:continue
  used=set();todo=[left,right]
  while todo:
   v=todo.pop()
   if v in used:continue
   used.add(v)
   if v in defs:todo.extend(defs[v])
  if any(q not in used for q in helpers):continue
  rows=dict(base)
  for q,(a,z)in dict(defs,**{}).items():rows[q,0]=(0,True,a);rows[q,1]=(1,True,z)
  rows[190,0]=(0,True,left);rows[190,1]=(1,True,right)
  ops=c.opportunities_fast(rows,{q:None for q,bit in rows})
  matching=c.max_matching(ops)
  score=len(rows)//2-len(matching);total+=1
  if score<=194:
   candidate=dict(k=k,helpers=defs,root=[left,right],score=score,folds=len(matching),pairs=matching)
   records.append(candidate)
   print(json.dumps(candidate),flush=True)
  if score<best:best=score;print('BEST',best,'cases',total,'elapsed',time.monotonic()-started,file=sys.stderr,flush=True)
 if len(helpers)==hmax:return
 q=330+len(helpers)
 for a,z in itertools.product(choices,repeat=2):
  if(a,z)==(61,61)or(a,z)in defs.values():continue
  if counts[a]+counts[z]>32:continue
  visit(helpers+[q],counts|{q:counts[a]+counts[z]},defs|{q:(a,z)},hmax)
if __name__=='__main__':
 n=int(sys.argv[1])if len(sys.argv)>1 else 3
 visit([],{61:1,99:2},{},n)
 result=dict(max_helpers=n,number_candidates=total,best=best,results=records,elapsed_seconds=time.monotonic()-started)
 (HERE/f'addition_search{n}.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result),file=sys.stderr)
