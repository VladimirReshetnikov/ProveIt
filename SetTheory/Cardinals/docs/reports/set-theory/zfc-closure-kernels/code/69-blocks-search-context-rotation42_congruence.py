#!/usr/bin/env python3
"""One bounded origin-prioritized congruence quotient of source rotation 42.
All universally inspected literal rows and the 42 fixed macro rows are kept.
Successful quotients are freshly replayed; no blank initialization is claimed.
"""
from pathlib import Path
from functools import lru_cache
from itertools import combinations
import json
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
code = ROOT / 'code'
sys.path.insert(0, str(code))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from recompile_decoder import (A, MACRO, NODES, OLD, PAIRS, T, Track,
                               emit, get_sites, make_cases)
from recompile_decoder import ROOT as SOURCE_ROOT
import rotate_search as rot

def mutate_origins(nodes,root,n,exp):
 new={};seen={};origins={}
 def intern(a,b):
  pair=a,b
  if pair not in seen:seen[pair]=len(new);new[seen[pair]]=pair
  return ('N',seen[pair])
 @lru_cache(None)
 def edge(e):
  if e[0]=='N':
   z=edge(exp) if e[1]==n else intern(*(edge(c) for c in nodes[e[1]]))
   origins.setdefault(z[1],set()).add(e[1]);return z
  if e[0]=='T':return intern(edge(e[1]),edge(e[2]))
  return e
 return new,edge(('N',root))[1],origins

idx=42;n,exp,kind=rot.options(NODES)[idx]
nodes,root,origins=mutate_origins(NODES,SOURCE_ROOT,n,exp)
U,metadata,entries=emit(nodes,root,generic=False)
C=make_cases(get_sites(nodes,root));tracked=Track(U);tracked.used=set()
for p,branch,target,halt in C:A.run(tracked,p,branch,target,halt=halt,fuel=2000)
live=tracked.used|PAIRS;states={q for q,b in live};print('INITIAL',len(states),'rows',len(live),flush=True)
fixed={str(q) for q in MACRO}|{'96'}
initial_parent={q:q for q in states|{'254'}}
initial_rows={q:{} for q in states|{'254'}}
for q,b in live:initial_rows[q][b]=U[q,b]

def find(parent,q):
 while parent[q]!=q:q=parent[q]
 return q

def trial(parent,rows,a,b):
 parent=parent.copy();rows={q:r.copy() for q,r in rows.items()};todo=[(a,b)];unions=[]
 while todo:
  a,b=todo.pop();a,b=find(parent,a),find(parent,b)
  if a==b:continue
  if a in ('254','96') or b in ('254','96'):return None
  if a in fixed and b in fixed:return None
  if b in fixed or (a not in fixed and int(a)>int(b)):a,b=b,a
  ra,rb=rows[a],rows[b]
  for bit in ra.keys()&rb.keys():
   x,y=ra[bit],rb[bit]
   if x[:2]!=y[:2]:return None
   todo.append((x[2],y[2]))
  parent[b]=a;unions.append((b,a))
  ra.update({k:v for k,v in rb.items() if k not in ra});del rows[b]
 return parent,rows,unions

origin_pairs=[]
for nn,oldnodes in origins.items():
 for old in oldnodes:
  for oq in OLD['state_entries'][str(old)]:
   nq=entries[nn]
   if oq in states and nq in states and oq!=nq:origin_pairs.append((oq,nq))
origin_pairs=list(dict.fromkeys(origin_pairs))
start=time.monotonic();records=[];best=999
for ordername,priority in [('origins',origin_pairs),('reverse_origins',list(reversed(origin_pairs)))]:
 parent=initial_parent.copy();rows={q:r.copy() for q,r in initial_rows.items()};accepted=[];tests=0;cutoff=False
 for a,b in priority+list(combinations(sorted(states,key=int),2)):
  if time.monotonic()-start>110:cutoff=True;break
  if find(parent,a)==find(parent,b):continue
  tests+=1;z=trial(parent,rows,a,b)
  if z is not None:
   parent,rows,unions=z;accepted.append(dict(seed=(a,b),forced=unions))
 Q={}
 for q,rr in rows.items():
  if q=='254':continue
  for bit in (0,1):
   if bit in rr:w,d,t=rr[bit];Q[q,bit]=(w,d,find(parent,t))
   else:Q[q,bit]=(0,'L','95')
 assert all(Q[e]==T[e] for e in PAIRS)
 failure=None
 for p,branch,target,halt in C:
  try:A.run(Q,p,branch,target,halt=halt,fuel=2000)
  except Exception as ex:failure=dict(pc=p,branch=branch,message=str(ex));break
 size=len(Q)//2;record=dict(order=ordername,states=size,tests=tests,accepted=accepted,cutoff=cutoff,failure=failure,seconds=time.monotonic()-start)
 records.append(record);print('RESULT',ordername,size,'tests',tests,'accepted',len(accepted),'cutoff',cutoff,'failure',failure,flush=True)
 if failure is None and size<best:
  best=size;out=Path(__file__).with_name('rotation42-quotient-'+str(size));out.mkdir(exist_ok=True)
  (out/'dag.json').write_text(json.dumps(dict(root=root,nodes=nodes,index=42,node=n,expression=exp),indent=2)+'\n')
  (out/'machine.tm').write_text('#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(Q.items(),key=lambda x:(int(x[0][0]),x[0][1]))))
  (out/'quotient.json').write_text(json.dumps(dict(parent={q:find(parent,q) for q in parent},rows_before=len(live),record=record),indent=2)+'\n')
 if cutoff or best<246:break
result=dict(status='COMPLETE_BOUNDED_PASS',initial_states=len(states),live_rows=len(live),source_nodes=len(nodes),origin_pairs=len(origin_pairs),best_initialized_states=best,records=records,blank_start_verified=False)
Path(__file__).with_name('rotation42-congruence-results.json').write_text(json.dumps(result,indent=2)+'\n')
