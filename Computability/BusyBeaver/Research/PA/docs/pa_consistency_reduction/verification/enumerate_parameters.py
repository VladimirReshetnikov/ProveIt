import optimize_parameters as O
import itertools,json,time,sys
from pathlib import Path
base=O.tree('x67');perms=list(itertools.permutations('HAD'));bounds=[18,35,54,70,86,102,121]
leaves=[]
def collect(t,offset=0):
 if isinstance(t,str):return [(offset,t)]
 return collect(t[0],offset)+collect(t[1],offset+O.width(t[0]))
def changed(t,key,offset=0):
 if isinstance(t,str):
  for i in range(6):
   if bounds[i]<=offset<bounds[i+1]:return dict(zip('HAD',perms[key[i]])).get(t,t)
  return t
 return changed(t[0],key,offset),changed(t[1],key,offset+O.width(t[0]))
best=196;start=time.monotonic();tested=0
for i,key in enumerate(itertools.product(range(6),repeat=6)):
 t=changed(base,key)
 if len(O.nodes(t))>76:continue
 tested+=1;s,n,c,ds=O.evaluate(t)
 if s<best:
  best=s;p=Path(__file__).with_name(f'enumerated_parameters_{s}_{i}.json');O.output(t,tuple(range(6)),p)
  print('BEST',s,n,c,key,ds,'secs',time.monotonic()-start,flush=True)
  if best<196:break
 if i%3000==0:print('progress',i,'tested',tested,'best',best,'seconds',time.monotonic()-start,flush=True)
print('DONE',i,tested,best,time.monotonic()-start,flush=True)
