from itertools import product,permutations
from math import factorial
from collections import defaultdict
from core_templates import preorders
import json,time
from pathlib import Path

def weakcomps(total,d):
 if d==0:
  if total==0:yield ()
  return
 for a in range(total+1):
  for c in weakcomps(total-a,d-1):yield (a,)+c

def transitive(arcs,n):
 return all((i,k)in arcs for i,j in arcs for a,k in arcs if j==a)

def templates():
 seen=set()
 for core in preorders(3):
  for signs in product((-1,0,1),repeat=3):
   types=[]
   for mask in range(1,8):
    if any(mask>>i&1 and signs[i]==0 for i in range(3)):continue
    arcs=core|{(3,3)}
    for i in range(3):
     if mask>>i&1:arcs.add((i,3)if signs[i]==-1 else(3,i))
    if transitive(arcs,4):types.append(mask)
   # Keep signature of actual directed relation; orientation of isolated core irrelevant.
   arcs=set(core)
   for t,mask in enumerate(types):
    for i in range(3):
     if mask>>i&1:arcs.add((i,3+t)if signs[i]==-1 else(3+t,i))
   key=tuple(sorted(arcs))
   if key not in seen:seen.add(key);yield core,signs,types

def support_polys(core,signs,types):
 d=len(types);g=[defaultdict(int)for _ in range(4)]
 for r in range(4):
  for quota in weakcomps(r,d):
   masks=[t for t,n in zip(types,quota)for _ in range(n)]
   def edge(i,j):
    if i<3 and j<3:return i!=j and(i,j)in core
    if i<3<=j:return signs[i]==-1 and masks[j-3]>>i&1
    if j<3<=i:return signs[j]==1 and masks[i-3]>>j&1
    return False
   for rc in product((0,1,2),repeat=3):
    for re in product((1,2),repeat=r):
     roles=rc+re;A=[i for i,a in enumerate(roles)if a==1];B=[i for i,a in enumerate(roles)if a==2];k=len(A)
     if k!=len(B)or k>3:continue
     if any(all(edge(i,j)for i,j in zip(A,p))for p in permutations(B)):g[k][quota]+=1
 return [dict(a)for a in g]

def bprod(a,b):
 for js in product(*(range(min(i,j)+1)for i,j in zip(a,b))):
  c=tuple(i+j-k for i,j,k in zip(a,b,js));v=1
  for i,j,k in zip(a,b,js):v*=factorial(i+j-k)//(factorial(k)*factorial(i-k)*factorial(j-k))
  yield c,v

def mul(A,B):
 C=defaultdict(int)
 for a,u in A.items():
  for b,v in B.items():
   for c,w in bprod(a,b):C[c]+=u*v*w
 return C

def gap(A,B,C,ratio):
 D=mul(B,B)
 for r,v in mul(A,C).items():D[r]-=ratio*v
 return {r:v for r,v in D.items()if v}

if __name__=='__main__':
 start=time.time();bad=[];counts=defaultdict(int);ts=list(templates())
 print('templates',len(ts),flush=True)
 for idx,(core,signs,types)in enumerate(ts):
  g=support_polys(core,signs,types)
  if not g[3]:continue
  D=gap(g[1],g[2],g[3],3);negs={str(r):v for r,v in D.items()if v<0}
  counts[len(types)]+=1
  if negs:bad.append({'core':sorted(core),'signs':signs,'types':types,'negative':negs})
  if idx%50==0:print(idx,'bad',len(bad),'secs',time.time()-start,flush=True)
 Path(__file__).with_name('cover3_scan.json').write_text(json.dumps({'templates':len(ts),'degree3_templates_by_types':dict(counts),'bad':bad,'seconds':time.time()-start},indent=2)+'\n')
 print('FINAL',dict(counts),'bad',len(bad),'secs',time.time()-start)
 if bad:print(bad[:2])
