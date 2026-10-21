#!/usr/bin/env python3
"""Exact full blank replay and independent complete zero-PC seed decoding."""
import json,gzip
from pathlib import Path
from reconstruct import table
ROOT=Path(__file__).resolve().parent.parent
PHY=(6,2,0,4,3,7,8,5,1)
def check():
 T=table(ROOT/'machine/k215.native.tm');C=table(ROOT/'machine/k215.tm');N=table(ROOT/'machine/k215.normalized.tm');m=json.loads((ROOT/'machine/canonicalization.json').read_text());cm={int(k):v for k,v in m['native_to_canonical'].items()};nm={int(k):v for k,v in m['normalized_to_native'].items()};Q={q for q,b in T}
 assert len(Q)==215 and len(T)==430 and{z for w,d,z in T.values()}-Q=={254};assert all((q,b)in T for q in Q for b in(0,1))
 assert len(cm)==len(set(cm.values()))==216 and cm[0]==0 and cm[254]==215 and set(cm.values())==set(range(216))
 assert {(cm[q],b):(w,d,cm[z])for(q,b),(w,d,z)in T.items()}==C
 assert {(nm[q],b):(w,d,nm[z])for(q,b),(w,d,z)in N.items()}==T
 seen={0};todo=[0]
 while todo:
  q=todo.pop()
  for b in(0,1):
   z=T[q,b][2]
   if z!=254 and z not in seen:seen.add(z);todo.append(z)
 assert seen==Q
 st=json.loads(gzip.decompress((ROOT/'evidence/startup.json.gz').read_bytes()));seed=json.loads((ROOT/'evidence/root_seed.json').read_text());assert st['steps']==716307 and len(st['trace'])==st['steps'];q=h=0;ones=set()
 for k in range(st['steps']):
  b=int(h in ones);w,d,z=T[q,b];di=1 if d=='R'else-1;assert st['trace'][k]==[q,h,b,w,di,z]
  if w:ones.add(h)
  else:ones.discard(h)
  q,h=z,h+di
 assert q==84 and h==-9 and sorted(ones)==st['one_cells']==seed['one_cells'];assert min(ones)==h-1
 header=min(x for x in ones if x>h-1);assert header>=h+64 and header-h-64==152
 p=header+1;last=max(ones);values=[]
 while p<=last:
  assert p not in ones and p+1 in ones;p+=1;n=0
  while p in ones:n+=1;p+=1
  values.append(n-1)
 assert p==last+1 and len(values)>=10
 regs=[values[i]for i in PHY];assert regs==[4,0,0,0,1,0,0,0,0]==st['registers']==seed['registers']
 assert values[9:]==st['spares']==seed['spares']and len(values[9:])==185 and len(ones)==386
 return dict(status='EXACT_BLANK_ZERO_PC_ROOT_PASS',working_states=215,rows=430,reachable_states=215,steps=716307,head=h,gap=152,registers=regs,spare_count=185,one_count=386,scope='Exact whole-tape finite replay. State84 plus complete64-zero-PC and complete unary-frame decoding; no clean-dispatch heuristic. Source soundness/completeness from this D=1 seed is an explicit separate argument.')
