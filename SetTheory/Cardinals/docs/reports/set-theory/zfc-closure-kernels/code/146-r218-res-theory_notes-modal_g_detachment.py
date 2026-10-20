#!/usr/bin/env python3
"""Sound bounded CD+GEN screen for G plus fixed-binder rho2/rho6.

Only positive replayed derivations establish a calibration. Failure within
these size/modal-depth/time bounds is not a countermodel.
"""
from pathlib import Path
from functools import lru_cache
import argparse,heapq,json,time

def C(a,b):return('C',a,b)
def Q(a):return('Q',a)
@lru_cache(None)
def size(t):return 1+sum(size(x)for x in t[1:])if isinstance(t,tuple)else 1
@lru_cache(None)
def depth(t):
 if not isinstance(t,tuple):return 0
 return (t[0]=='Q')+max(map(depth,t[1:]))
@lru_cache(None)
def nvars(t):
 if isinstance(t,tuple):return max(map(nvars,t[1:]))
 return t+1 if isinstance(t,int)else 0

def canonical(t):
 variables={}
 def go(x):
  if isinstance(x,tuple):return(x[0],)+tuple(map(go,x[1:]))
  return variables.setdefault(x,len(variables))if isinstance(x,int)else x
 return go(t)

def rename(t,n):
 if isinstance(t,tuple):return(t[0],)+tuple(rename(x,n)for x in t[1:])
 return t+n if isinstance(t,int)else t

def detach(major,minor):
 if not isinstance(major,tuple)or major[0]!='C':return None
 minor=rename(minor,nvars(major));bindings={}
 def deref(t):
  while isinstance(t,int)and t in bindings:t=bindings[t]
  return t
 def occurs(v,t):
  t=deref(t)
  return any(occurs(v,x)for x in t[1:])if isinstance(t,tuple)else t==v
 stack=[(major[1],minor)]
 while stack:
  x,y=map(deref,stack.pop())
  if x==y:continue
  if isinstance(y,int)and not isinstance(x,int):x,y=y,x
  if isinstance(x,int):
   if occurs(x,y):return None
   bindings[x]=y
  elif isinstance(x,tuple)and isinstance(y,tuple)and x[0]==y[0]:stack.extend(zip(x[1:],y[1:]))
  else:return None
 def sub(t):
  t=deref(t)
  return(t[0],)+tuple(map(sub,t[1:]))if isinstance(t,tuple)else t
 return canonical(sub(major[2]))

def subsumes(p,t):
 bindings={};stack=[(p,t)]
 while stack:
  x,y=stack.pop()
  if isinstance(x,int):
   if x in bindings:
    if bindings[x]!=y:return False
   else:bindings[x]=y
  elif isinstance(x,tuple):
   if not isinstance(y,tuple)or x[0]!=y[0]:return False
   stack.extend(zip(x[1:],y[1:]))
  elif x!=y:return False
 return True

def word(t):
 if isinstance(t,tuple):return t[0]+''.join(map(word,t[1:]))
 return str(t)+','if isinstance(t,int)else t

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--maxsize',type=int,default=25);ap.add_argument('--depth',type=int,default=3);ap.add_argument('--steps',type=int,default=2000);ap.add_argument('--seconds',type=float,default=90);args=ap.parse_args()
 a,b,c=0,1,2;G=C(C(C(a,b),a),C(c,a));M=C(Q(C(a,b)),C(Q(a),Q(b)));D=C(C(Q(C(Q(a),'f')),'f'),a)
 targets={'K':C(a,C(b,a)),'P':C(C(C(a,b),a),a),'H':C(C(a,b),C(C(b,c),C(a,c))),'L':C(C(C(a,b),c),C(C(c,a),C(3,a)))}
 nodes=[];known={};pending=[];processed=[];found={};byhead={};start=time.monotonic()
 def add(t,p):
  if t is None or size(t)>args.maxsize or depth(t)>args.depth or t in known:return
  head=t[0]if isinstance(t,tuple)else type(t)
  if any(size(u)<=size(t)and subsumes(u,t)for u in byhead.get(head,())):return
  i=len(nodes);known[t]=i;byhead.setdefault(head,[]).append(t);nodes.append((t,p));heapq.heappush(pending,(size(t),i))
  for name,target in targets.items():
   if name not in found and subsumes(t,target):found[name]=i;print('FOUND',name,i,word(t),flush=True)
 for t in (G,M,D,'t'):add(canonical(t),'axiom')
 while pending and len(processed)<args.steps and time.monotonic()-start<args.seconds:
  _,i=heapq.heappop(pending);x=nodes[i][0];add(Q(x),['GEN',i])
  for j in processed+[i]:
   y=nodes[j][0];add(detach(x,y),[i,j])
   if i!=j:add(detach(y,x),[j,i])
  processed.append(i)
  if len(processed)%100==0:print('PROGRESS',len(processed),len(nodes),round(time.monotonic()-start,2),flush=True)
  if {'K','P','H'}<=found.keys()or'L'in found:break
 for t,p in nodes:
  if p=='axiom':continue
  assert(Q(nodes[p[1]][0])if p[0]=='GEN'else detach(nodes[p[0]][0],nodes[p[1]][0]))==t
 result=dict(bounds=vars(args),seconds=time.monotonic()-start,processed=len(processed),nodes=len(nodes),found=found,derivations=[dict(formula=word(t),term=t,proof=p)for t,p in nodes])
 (Path(__file__).parent/'modal_g_detachment.json').write_text(json.dumps(result,indent=2)+'\n');print('DONE',{k:v for k,v in result.items()if k!='derivations'},flush=True)
if __name__=='__main__':main()
