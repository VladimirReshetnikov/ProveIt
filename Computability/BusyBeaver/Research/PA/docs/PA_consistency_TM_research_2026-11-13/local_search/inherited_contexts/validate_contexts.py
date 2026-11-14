#!/usr/bin/env python3
"""Independent finite regression checks for the source-context collector.

These checks detect implementation mistakes. They are not the unbounded
soundness argument; that is the symbolic whole-tape induction being inspected.
"""
from pathlib import Path
import importlib.util,json,random,sys,time
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'sources/ProveIt/Computability/BusyBeaver/Research/PA/pa196-vs-u208'
HERE=Path(__file__).resolve().parent
I=HERE/'inputs'
FOLD=I/'scan_local_folds.py' if I.exists() else BASE/'search/scan_local_folds.py'
TABLE=I/'pa196.tm' if I.exists() else ROOT/'sources/BusyBeaver/data/pa196.tm'
SOURCE=I/'original.json' if I.exists() else BASE/'source-search/allocator-screen/original.json'
spec=importlib.util.spec_from_file_location('fold',FOLD);f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
T,_=f.read_table(TABLE)
C={q:set()for q in range(196)}
for line in (HERE/'source_contexts.txt').read_text().splitlines():
 q,b,m=map(int,line.split());assert b==(m>>2)&1;C[q].add(m)
closure,_,_=f.blank_window_contexts(T,6)
G={q:set()for q in range(196)}
for (q,b),xs in closure.items():G[q].update(sum(t[i]<<(i+2)for i in range(-2,3))for t in xs)
S=json.loads(SOURCE.read_text())
PHY=(6,2,0,4,3,7,8,5,1)

def frame(path,gap,values,head=0):
 ones={head-1,head+gap}
 ones.update(head+i for i,b in enumerate(path)if b=='1');pos=head+gap+1
 for v in values:
  ones.update(range(pos+1,pos+v+2));pos+=v+2
 return ones

def increment(p):
 if not p:return '',1
 i=int(p,2)+1;return f'{i%(1<<len(p)):0{len(p)}b}',int(i==(1<<len(p)))

def strip(p,bit,n):
 for k in range(len(p)-1,-1,-1):
  if p[k]==bit:
   n-=1
   if n==0:return p[:k]
 return ''

rng=random.Random(19620261113);cases=0;steps=0;compared=0;start=time.monotonic()
fixtures=[(i,0)for i in range(0,len(S),17)]+[(rng.randrange(len(S)),rng.randrange(3))for _ in range(128)]
for i,kind in fixtures:
 path,op,arg=S[i];values=[0]*9 if kind==0 else [rng.randrange(20 if kind==1 else 200)for _ in range(9)]
 physical=[0]*9
 for r,p in enumerate(PHY):physical[p]=values[r]
 physical += [rng.randrange(5) for _ in range(1+rng.randrange(6))]
 after=list(physical);gap=48+rng.randrange(20);delta=0;overflow=0
 if op=='CI':
  after[PHY[arg]]+=1;after.append(1);succ,overflow=increment(path)
 elif op=='CD' and values[arg]>0:
  after[PHY[arg]]-=1;delta=1;succ,overflow=increment(path)
 elif op in ('CD','CB'):succ,overflow=increment(strip(path,'0',1 if op=='CD'else arg))
 elif op=='CC':succ=strip(path,'1',arg)
 else:succ=''
 tape=frame(path,gap,physical);target=frame(succ,gap+delta+overflow,after,-overflow)
 q=75;head=0
 for n in range(300000):
  if n and ((op=='CH'and q==196)or(op!='CH'and q==75 and head==-overflow and tape==target)):break
  assert q!=196,('unexpected halt',i)
  mask=sum(int(head+j in tape)<<(j+2)for j in range(-2,3))
  if mask in G[q]:
   assert mask in C[q],('missed concrete context',i,kind,n,q,mask)
   compared+=1
  b=int(head in tape);w,d,q=T[q,b]
  if w:tape.add(head)
  else:tape.discard(head)
  head+=d;steps+=1
 else:raise ValueError(('endpoint not reached',i,kind))
 cases+=1
receipt=dict(status='FINITE_CONCRETE_REGRESSION_PASS',cases=cases,full_tape_steps=steps,window_checks_within_global_invariant=compared,seconds=time.monotonic()-start,scope='Finite independent regression only; unbounded context inclusion requires the supplied symbolic argument.')
(HERE/'validation_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
