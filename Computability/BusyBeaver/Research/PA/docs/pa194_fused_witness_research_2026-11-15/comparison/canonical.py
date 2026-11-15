#!/usr/bin/env python3
"""Exact whole-graph comparison under deliberately broad structural symmetries.

A graph with one source strongly connected component has spanning roots
exactly in that component. This avoids trying every control needlessly.
Read-bit labels and actions are compared exactly, except that the broad
key allows tape reflection, global bit exchange, and ignores halt-entry
write/move decorations. Bit exchange is a structural comparison only:
it is not asserted to preserve a zero-blank computation.
"""
from pathlib import Path
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent

def sha(b):return hashlib.sha256(b).hexdigest()
def parse(path):
 rows={}
 for line in path.read_text().splitlines():
  if not line.strip() or line.lstrip().startswith('#'):continue
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
  if (q,b) in rows or b not in (0,1) or w not in (0,1) or d not in ('L','R'):raise ValueError('invalid table')
  rows[q,b]=(w,d,n)
 states={q for q,b in rows}
 if len(rows)!=2*len(states) or any((q,b) not in rows for q in states for b in (0,1)):raise ValueError('incomplete table')
 if len({n for w,d,n in rows.values()}-states)!=1:raise ValueError('expected unique terminal control')
 return rows,states

def spanning_roots(rows,states):
 adj={q:{rows[q,b][2] for b in (0,1)}&states for q in states}
 rev={q:set()for q in states}
 for q,outs in adj.items():
  for n in outs:rev[n].add(q)
 seen=set();order=[]
 def visit(q):
  if q in seen:return
  seen.add(q)
  for n in adj[q]:visit(n)
  order.append(q)
 for q in sorted(states):visit(q)
 comps=[];component={}
 for q in reversed(order):
  if q in component:continue
  index=len(comps);stack=[q];component[q]=index;members=[]
  while stack:
   n=stack.pop();members.append(n)
   for v in rev[n]:
    if v not in component:component[v]=index;stack.append(v)
  comps.append(members)
 incoming=set()
 for q,outs in adj.items():
  for n in outs:
   if component[q]!=component[n]:incoming.add(component[n])
 sources=[i for i in range(len(comps)) if i not in incoming]
 return sorted(comps[sources[0]])if len(sources)==1 else []

def rooted(rows,states,start,mirror=False,flip=False,loose=False):
 index={start:0};order=[start];out=[]
 for q in order:
  for b in(0,1):
   w,d,n=rows[q,b^int(flip)];w^=int(flip)
   if mirror:d='L'if d=='R'else'R'
   if n in states:
    if n not in index:index[n]=len(order);order.append(n)
    out.append((w,d,index[n]))
   else:out.append((0,'R',-1)if loose else(w,d,-1))
 return tuple(out)

def least_bfs(rows,states,roots,options,loose=False):
 # Lexicographic branch pruning: after a prefix first exceeds the best
 # complete tuple, no unseen suffix can make this root a minimum.
 best=None
 for mirror,flip in options:
  for start in roots:
   index={start:0};order=[start];out=[];cmp=0;reject=False
   for q in order:
    for b in(0,1):
     w,d,n=rows[q,b^int(flip)];w^=int(flip)
     if mirror:d='L'if d=='R'else'R'
     if n in states:
      if n not in index:index[n]=len(order);order.append(n)
      triple=(w,d,index[n])
     else:triple=(0,'R',-1)if loose else(w,d,-1)
     if best is not None and cmp==0:
      prior=best[len(out)]
      if triple>prior:reject=True;break
      if triple<prior:cmp=-1
     out.append(triple)
    if reject:break
   if not reject:
    value=tuple(out)
    if best is None or value<best:best=value
 return best

def canonical(rows,states,mirror=False,flip=False,loose=False):
 return least_bfs(rows,states,spanning_roots(rows,states),[(mirror,flip)],loose)
def key(rows,states,broad=False):
 roots=spanning_roots(rows,states)
 if not roots:return None
 options=[(m,f)for m in(False,True)for f in(False,True)]if broad else[(False,False)]
 value=least_bfs(rows,states,roots,options,broad)
 return sha(json.dumps(value,separators=(',',':')).encode())

