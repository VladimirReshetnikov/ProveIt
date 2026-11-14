"""Inductive small-constant interval analysis, combined with relational zeros."""
import json,sys,time,collections
from pathlib import Path
from paths import INPUTS,OUT
import source_language as L
sites=json.loads((INPUTS/'sites.json').read_text());graph=L.graph_intervals(sites);CAP=16;seed=(1,0,13,0,0,1,0,0,1)
# Upper endpoint CAP denotes infinity; lower endpoint CAP denotes >=CAP.
def trans(st,e,b):
 out=list(st)
 if e[0]=='increment':
  lo,hi=st[e[1]];out[e[1]]=(min(CAP,lo+1),min(CAP,hi+1))
 elif e[0]=='decrement':
  r=e[1];lo,hi=st[r]
  if b:
   if hi==0:return None
   out[r]=(max(1,lo)-1,hi-1 if hi<CAP else CAP)
  else:
   if lo:return None
   out[r]=(0,0)
 return tuple(out)
started=time.monotonic();states=[None]*len(sites);states[136]=tuple((v,v)for v in seed);todo=collections.deque([136]);updates=0
while todo:
 i=todo.popleft();e,targets=graph[i]
 for branch,j in enumerate(targets):
  new=trans(states[i],e,branch)
  if new is None:continue
  old=states[j];joined=new if old is None else tuple((min(a[0],b[0]),max(a[1],b[1]))for a,b in zip(old,new))
  if joined!=old:states[j]=joined;todo.append(j);updates+=1
for i,st in enumerate(states):
 if st is None:continue
 e,targets=graph[i]
 for b,j in enumerate(targets):
  image=trans(st,e,b)
  if image is not None:assert states[j]is not None and all(a[0]>=z[0]and a[1]<=z[1]for a,z in zip(image,states[j]))
zero=json.loads((OUT/'source_relational_invariant.json').read_text())['conditional_facts'];facts={};strengthened=[]
for i,(pc,op,arg)in enumerate(sites):
 for branch in([0,1]if op=='CD'else[0]):
  z=zero[f'{i}:{branch}'];st=states[i]
  if st is None or z is None:facts[f'{i}:{branch}']=None;continue
  f=[]
  for j,(lo,hi)in enumerate(st):
   if z[j]==1:lo=hi=0
   elif z[j]==2:lo=max(lo,1)
   if lo>hi:f=None;break
   f.append([lo,hi])
  facts[f'{i}:{branch}']=f
  if f is not None and any(lo>1 or(lo==hi==1)for lo,hi in f):strengthened.append([i,branch])
result={'status':'INDUCTIVE_SMALL_CONSTANT_INTERVALS','cap':CAP,'cap_semantics':'upper infinity, lower at least16','seed':seed,'updates':updates,'conditional_intervals':facts,'strengthened_cases':len(strengthened),'seconds':time.monotonic()-started}
(OUT/'source_intervals.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items()if k!='conditional_intervals'})
for i in(0,7,44,364,579,3255,3748):print(i,facts[f'{i}:0'])
