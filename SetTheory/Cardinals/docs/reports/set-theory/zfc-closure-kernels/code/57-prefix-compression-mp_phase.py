#!/usr/bin/env python3
"""Compute a checked finite abstract post-fixpoint for the MP rewrite."""
from pathlib import Path
import json,sys
from collections import defaultdict,deque
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source/Computability/BusyBeaver/Research/ZFC'))
import permutation252_phase_analysis as p
nodes=json.loads((ROOT/'redesign/mp_runtime/modified-tree.json').read_text())
sites=[]
def visit(q,pc):
 for b,e in enumerate(nodes[q]):
  op,*a=e.split();arg=int(a[0]) if a else None;path=pc+str(b)
  if op=='CN':visit(arg,path)
  else:sites.append((path,op,arg))
visit(0,'')
lookup={pc:i for i,(pc,op,r) in enumerate(sites)}
def decode(pc):
 q=0;path=''
 while True:
  bit=pc[len(path)] if len(path)<len(pc) else '0';path+=bit
  op,*a=nodes[q][int(bit)].split()
  if op=='CN':q=int(a[0])
  else:
   assert '1' not in pc[len(path):]
   return lookup[path]
cases=[];targets=[]
for site,(path,op,r) in enumerate(sites):
 for zero in ((True,False) if op=='CD' else (None,)):
  cases.append((site,path,op,r,zero))
  pc=p.successor(path,op,r,zero)
  targets.append(None if pc is None else decode(pc))
by_site=defaultdict(list)
for i,case in enumerate(cases):by_site[case[0]].append(i)
first=decode('');values=[None]*len(sites);values[first]=(1,)*9
pending=deque([first]);pops=0
while pending:
 site=pending.popleft();pops+=1
 for i in by_site[site]:
  target=targets[i]
  if target is None:continue
  result=p.transfer(values[site],cases[i])
  if result is None:continue
  old=values[target];joined=result if old is None else tuple(a|b for a,b in zip(old,result))
  if old!=joined:values[target]=joined;pending.append(target)
assert first==0 and all(mask&1 for mask in values[first])
excluded=[];edges=0
for i,(case,target) in enumerate(zip(cases,targets)):
 old=values[case[0]];result=None if old is None else p.transfer(old,case)
 if result is None:excluded.append(i)
 elif target is not None:
  assert values[target] is not None
  assert all(a&~b==0 for a,b in zip(result,values[target]));edges+=1
result={'scope':'Ordinary finite post-fixpoint check for the rewritten source program from zeroRoot; not a kernel proof and not a binary startup certificate.',
        'sites':len(sites),'guards':len(cases),'pops':pops,'checked_edges':edges,
        'excluded':[dict(index=i,path=cases[i][1],op=cases[i][2],register=cases[i][3],zero=cases[i][4]) for i in excluded]}
out=ROOT/'compression/mp_phase.json';out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
