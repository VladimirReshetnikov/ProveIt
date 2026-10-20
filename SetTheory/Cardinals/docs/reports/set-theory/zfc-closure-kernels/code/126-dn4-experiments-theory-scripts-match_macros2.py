import explore_source as e
import json
from collections import defaultdict,Counter
from functools import cache
b=e.b
root=b.tree(json.loads(e.BASELINE_SOURCE.read_text()))
@cache
def fingerprint(n):
 try:
  rows,g,i=b.graph(b.sites(n)); g=list(g)
 except Exception:return None
 def compress(i):
  effects=Counter();seen=set()
  while g[i][0] in ('INC','JUMP'):
   if i in seen:return None
   seen.add(i)
   if g[i][0]=='INC':effects[g[i][1]]+=1;i=g[i][2]
   else:i=g[i][1]
  return i,tuple(sorted(effects.items()))
 queue=[];idx={}
 def add(i):
  if i not in idx:idx[i]=len(idx);queue.append(i)
  return idx[i]
 entry=compress(i)
 if entry is None:return None
 add(entry[0]);result=[]
 for i in queue:
  if g[i][0]=='HALT':result.append(('HALT',));continue
  _,r,t1,t2=g[i]
  c1=compress(t1);c2=compress(t2)
  if c1 is None or c2 is None:return None
  result.append(('DEC',r,(add(c1[0]),c1[1]),(add(c2[0]),c2[1])))
 return b.boundary(n),entry[1],tuple(result)
paths=defaultdict(list)
def walk(n,p=''):
 paths[n].append(p)
 if not b.is_leaf(n):walk(n[0],p+'0');walk(n[1],p+'1')
walk(root)
byfinger=defaultdict(list)
for n in paths:
 f=fingerprint(n)
 if f:byfinger[f].append(n)
if __name__=='__main__':
 for i,name in e.names.items():
  n=e.expand(('N',i));f=fingerprint(n)
  matches=byfinger.get(f,[]) if f else []
  if matches:print(i,name,[(len(paths[nn]),paths[nn][0],len(b.sites(nn))) for nn in matches])
  else:print(i,name,'NO MATCH')
