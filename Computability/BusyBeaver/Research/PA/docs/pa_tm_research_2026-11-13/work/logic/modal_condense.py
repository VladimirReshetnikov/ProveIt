#!/usr/bin/env python3
"""Bounded condensed-detachment experiment with one quantifier dimension."""
import heapq,itertools,json,time,sys
from pathlib import Path
I=lambda a,b:('i',a,b)
U=lambda a:('u',a)
F=('f',);T=('t',)
def size(t):return 1 if isinstance(t,int) else 1+sum(map(size,t[1:]))
def canon(t):
 d={}
 def go(t):
  if isinstance(t,int):
   if t not in d:d[t]=len(d)
   return d[t]
  return (t[0],*map(go,t[1:]))
 return go(t)
def offset(t,n):return t+n if isinstance(t,int) else(t[0],*(offset(x,n)for x in t[1:]))
def detach(p,q):
 if isinstance(p,int)or p[0]!='i':return
 q=offset(q,100000);subst={};jobs=[(p[1],q)]
 def deref(t):
  while isinstance(t,int)and t in subst:t=subst[t]
  return t
 def occurs(v,t):
  t=deref(t)
  return t==v if isinstance(t,int)else any(occurs(v,x)for x in t[1:])
 while jobs:
  a,b=map(deref,jobs.pop())
  if a==b:continue
  if isinstance(a,int):
   if occurs(a,b):return
   subst[a]=b
  elif isinstance(b,int):
   if occurs(b,a):return
   subst[b]=a
  elif a[0]!=b[0]:return
  else:jobs.extend(zip(a[1:],b[1:]))
 def close(t):
  t=deref(t)
  return t if isinstance(t,int)else(t[0],*map(close,t[1:]))
 return canon(close(p[2]))
def match(p,q):
 d={};todo=[(p,q)]
 while todo:
  a,b=todo.pop()
  if isinstance(a,int):
   if a in d and d[a]!=b:return False
   d[a]=b
  elif isinstance(b,int)or a[0]!=b[0]:return False
  else:todo.extend(zip(a[1:],b[1:]))
 return True
def fmt(t):
 if isinstance(t,int):return chr(97+t)
 if t[0]=='i':return '('+fmt(t[1])+'>'+fmt(t[2])+')'
 if t[0]=='u':return 'U'+fmt(t[1])
 return t[0]
P=I(I(I(0,1),0),0)
H1=I(I(U(I(U(0),F)),F),0)
H6=I(U(0),I(U(I(0,1)),U(1)))
ID=I(0,0)
K=I(0,I(1,0));S=I(I(0,I(1,2)),I(I(0,1),I(0,2)))
axioms=[P,H1,H6,ID,T]
limit=int(sys.argv[1])if len(sys.argv)>1 else 21
seen={};forms=[];parents=[];queue=[];active=[];found={};start=time.monotonic()
def add(p,proof):
 if p is None or p in seen or size(p)>limit:return
 i=len(forms);seen[p]=i;forms.append(p);parents.append(proof);heapq.heappush(queue,(size(p),i))
 for name,t in [('K',K),('S',S)]:
  if name not in found and match(p,t):found[name]=i;print('FOUND',name,i,fmt(p),'seconds',time.monotonic()-start,flush=True)
for i,p in enumerate(axioms):add(p,('axiom',i))
while queue and len(active)<2000 and len(found)<2:
 _,i=heapq.heappop(queue);p=forms[i]
 if any(match(forms[j],p)for j in active):continue
 add(U(p),('gen',i))
 for j in active+[i]:
  add(detach(p,forms[j]),('mp',i,j));add(detach(forms[j],p),('mp',j,i))
 active.append(i)
 if len(active)%100==0:print('progress',len(active),'seen',len(forms),'queue',len(queue),'seconds',time.monotonic()-start,flush=True)
result={'axioms':axioms,'forms':forms,'parents':parents,'found':found,'limit':limit,'active':len(active)}
Path(__file__).with_suffix('.result.json').write_text(json.dumps(result))
print('done',len(active),len(forms),found,'seconds',time.monotonic()-start,flush=True)
