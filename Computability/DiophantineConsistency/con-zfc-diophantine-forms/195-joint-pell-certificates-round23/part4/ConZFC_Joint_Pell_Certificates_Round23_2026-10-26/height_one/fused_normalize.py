"""Fuse constant and scale products directly into normalized source terms.
All retained constructors are triangular monic; dead ones are deleted.
"""
from copy import deepcopy
from collections import Counter
from product_constants import normalize as parent_normalize

def normalize(source,split=False,chain=True,mode='fused'):
 n=parent_normalize(source,split=split,chain=chain)
 vs=n['variables'];nv=n['original_variables'];cs={v['value']:i for i,v in enumerate(vs) if v['kind']=='constant'};sc={(v['coefficient'],v['variable']):i for i,v in enumerate(vs) if v['kind']=='scale'}
 defs={max(i for c,m in r['terms'] for i in m):r for r in n['rows'] if r['kind']!='source'}
 sr=[r for r in n['rows'] if r['kind']=='source']
 options=[]
 for r,original in zip(sr,source['residuals']):
  for t,(co,m) in zip(r['terms'],original['terms']):
   c=abs(co);choices={tuple(t[1])}
   if not m:
    for a,i in cs.items():
     if c%a==0 and c//a in cs:choices.add(tuple(sorted((i,cs[c//a]))))
   elif len(m)==1:
    x=m[0]
    if (c,x) in sc:choices.add((sc[c,x],))
    for a,i in cs.items():
     if c%a==0 and (c//a,x) in sc:choices.add((i,sc[c//a,x]))
   options.append((t,sorted(choices)))
 def used():
  out={i for r in sr for c,m in r['terms'] for i in m if i>=nv};todo=list(out)
  while todo:
   i=todo.pop()
   for c,m in defs[i]['terms']:
    for j in m:
     if j>=nv and j not in out:out.add(j);todo.append(j)
  return out
 def cost():
  live=used();return (len(live),sum(len(defs[i]['terms']) for i in live))
 if mode=='fused':
  for t,opts in options:
   old=t[1];best=(cost(),tuple(old))
   for p in opts:
    t[1]=list(p);z=(cost(),p)
    if z<best:best=z
   t[1]=list(best[1])
 elif mode=='scale_first':
  for t,opts in options:
   t[1]=list(min(opts,key=lambda p:(sum(i in cs.values() for i in p),len(p),p)))
 elif mode=='product_first':
  for t,opts in options:t[1]=list(min(opts,key=lambda p:(-len(p),max(p,default=-1),p)))
 for sweep in range(5):
  changed=False
  for t,opts in options:
   old=t[1];best=(cost(),tuple(old))
   for p in opts:
    t[1]=list(p);z=(cost(),p)
    if z[0]<best[0]:best=z
   t[1]=list(best[1]);changed|=(old!=t[1])
  if not changed:break
 live=used();keep=list(range(nv))+sorted(live);ren={i:j for j,i in enumerate(keep)}
 n['variables']=[vs[i] for i in keep];n['rows']=[defs[i] for i in sorted(live)]+sr
 for r in n['rows']:
  r['terms']=[[c,[ren[i] for i in m]] for c,m in r['terms']]
 n['constant_count']=sum(v['kind']=='constant' for v in n['variables']);n['scale_count']=sum(v['kind']=='scale' for v in n['variables'])
 return n
