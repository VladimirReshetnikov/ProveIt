#!/usr/bin/env python3
"""Small bounded condensed-detachment search; emitted proofs are explicit DAGs."""
import heapq,itertools,json,time,sys
from pathlib import Path
def imp(a,b):return(a,b)
def size(a):return 1 if isinstance(a,int) else 1+size(a[0])+size(a[1])
def canon(a):
 d={}
 def go(t):
  if isinstance(t,int):
   if t not in d:d[t]=len(d)
   return d[t]
  return(go(t[0]),go(t[1]))
 return go(a)
def offset(a,n):return a+n if isinstance(a,int) else(offset(a[0],n),offset(a[1],n))
def detach(p,q):
 if isinstance(p,int):return
 q=offset(q,10000);subst={};jobs=[(p[0],q)]
 def deref(t):
  while isinstance(t,int) and t in subst:t=subst[t]
  return t
 def occurs(v,t):
  t=deref(t)
  return v==t if isinstance(t,int) else occurs(v,t[0])or occurs(v,t[1])
 while jobs:
  a,b=map(deref,jobs.pop())
  if a==b:continue
  if isinstance(a,int):
   if occurs(a,b):return
   subst[a]=b
  elif isinstance(b,int):
   if occurs(b,a):return
   subst[b]=a
  else:jobs.extend(zip(a,b))
 def close(t):
  t=deref(t)
  return t if isinstance(t,int) else(close(t[0]),close(t[1]))
 return canon(close(p[1]))
def match(p,q):
 d={};todo=[(p,q)]
 while todo:
  a,b=todo.pop()
  if isinstance(a,int):
   if a in d and d[a]!=b:return False
   d[a]=b
  elif isinstance(b,int):return False
  else:todo.extend(zip(a,b))
 return True
def fmt(p):
 if isinstance(p,int):return chr(97+p) if p<26 else 'v'+str(p)
 return '('+fmt(p[0])+'>'+fmt(p[1])+')'
I=(0,0);T=(0,((0,1),1));P=(((0,1),0),0)
K=(0,(1,0));S=((0,(1,2)),((0,1),(0,2)))
axioms=[I,T,P]
limit=int(sys.argv[1])if len(sys.argv)>1 else 25
seen={};forms=[];parents=[];queue=[];active=[];found={};start=time.monotonic()
def add(p,proof):
 if p is None or p in seen or size(p)>limit:return
 i=len(forms);seen[p]=i;forms.append(p);parents.append(proof);heapq.heappush(queue,(size(p),i))
 for name,t in [('K',K),('S',S)]:
  if name not in found and match(p,t):
   found[name]=i;print('FOUND',name,i,fmt(p),'seconds',time.monotonic()-start,flush=True)
for i,p in enumerate(axioms):add(p,('axiom',i))
while queue and len(active)<5000 and len(found)<2:
 _,i=heapq.heappop(queue);p=forms[i]
 if any(match(forms[j],p)for j in active):continue
 for j in active+[i]:
  add(detach(p,forms[j]),('mp',i,j));add(detach(forms[j],p),('mp',j,i))
 active.append(i)
 if len(active)%100==0:print('progress',len(active),'seen',len(forms),'queue',len(queue),'seconds',time.monotonic()-start,flush=True)
result={'axioms':axioms,'forms':forms,'parents':parents,'found':found,'limit':limit,'active':len(active)}
Path(__file__).with_suffix('.result.json').write_text(json.dumps(result))
print('done',len(active),len(forms),found,'seconds',time.monotonic()-start,flush=True)
