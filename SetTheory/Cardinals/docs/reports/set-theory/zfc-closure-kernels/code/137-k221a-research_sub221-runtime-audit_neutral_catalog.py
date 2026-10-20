#!/usr/bin/env python3
"""Independent universal window proof for neutral single-row rewrites.

All-tape start window is unconstrained. Every shifted-in exterior bit is
branched both ways. Each neutral rewrite has positive old/new blocks with
identical complete tape and state/head; neither run reads outside the window
before joining. This is ordinary mathematical proof, not a kernel theorem.
"""
from pathlib import Path
from collections import deque,Counter
import json,hashlib,time
D=Path(__file__).resolve().parent; W=D.parents[1];P=W/'research_sub222/delivery/K221_Construction_2026-10-20/machine/k221.native.tm';L=R=5;MASK=(1<<11)-1;T={}
for ln in P.read_text().splitlines():
 if not ln or ln[0]=='#':continue
 q,b,w,d,z=ln.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
qs={q for q,b in T};assert len(qs)==221 and len(T)==442 and 254 not in qs
I={q:set()for q in qs|{254}};queue=deque((0,m)for m in range(MASK+1));I[0].update(range(MASK+1))
def successors(q,m):
 w,d,z=T[q,(m>>L)&1];x=(m&~(1<<L))|(w<<L)
 if d==1:a=x>>1;return z,(a,a|(1<<10))
 a=(x<<1)&MASK;return z,(a,a|1)
while queue:
 q,m=queue.popleft()
 if q==254:continue
 z,ms=successors(q,m)
 for mm in ms:
  if mm not in I[z]:I[z].add(mm);queue.append((z,mm))
for q in qs:
 for m in I[q]:
  z,ms=successors(q,m);assert all(mm in I[z]for mm in ms)
assert len(I[0])==2048

def step(q,h,m,patch):
 assert -L<=h<=R
 b=(m>>(L+h))&1;w,d,z=patch.get((q,b),T[q,b]);return z,h+d,(m&~(1<<(L+h)))|(w<<(L+h))

def audit(patch):
 assert len(patch)==1;e,row=next(iter(patch.items()));q,b=e;hist=Counter();count=0
 for m in sorted(I[q]):
  if(m>>L)&1!=b:continue
  count+=1;goals={};oq,oh,om=q,0,m
  for oldn in range(1,98):
   if oq==254 or not -L<=oh<=R:break
   oq,oh,om=step(oq,oh,om,{})
   goals.setdefault((oq,oh,om),oldn)
  nq,nh,nm=q,0,m
  for newn in range(1,98):
   if nq==254 or not-L<=nh<=R:raise ValueError(('new exits before join',e,row,m,newn))
   nq,nh,nm=step(nq,nh,nm,patch)
   oldn=goals.get((nq,nh,nm))
   if oldn is not None:hist[oldn,newn]+=1;break
  else:raise ValueError(('no positive join',e,row,m))
 assert count>0 and sum(hist.values())==count
 return {'row':list(e),'replacement':list(row),'contexts':count,'positive_old_new_blocks':[[a,b,n]for(a,b),n in sorted(hist.items())]}
start=time.monotonic();out=[]
for ln in(D/'neutral.txt').read_text().splitlines():
 q,b,w,d,z,n=map(int,ln.split());out.append(audit({(q,b):(w,d,z)}))
assert len(out)==516
try:audit({(0,0):(0,1,254)})
except ValueError as e:negative=str(e)
else:raise AssertionError('corrupt rewrite accepted')
record=dict(status='UNIVERSAL_NEUTRAL_ROW_CATALOG_AUDIT_PASS',baseline_sha256=hashlib.sha256(P.read_bytes()).hexdigest(),catalog_sha256=hashlib.sha256((D/'neutral.txt').read_bytes()).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),radius=5,fuel=97,initial_window='all 2048 bit patterns, arbitrary binary tape outside',inductive_window_contexts=sum(len(I[q])for q in qs),rewrites=len(out),total_row_contexts=sum(x['contexts']for x in out),seconds=time.monotonic()-start,negative_control=negative,results=out,scope='Each rewrite separately, from any tape in original inductive state-window invariant; entire-tape equality after positive old/new blocks. Composing rewrites or merging states requires another simultaneous proof.')
(D/'neutral_universal_audit.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:v for k,v in record.items()if k!='results'},indent=2))
