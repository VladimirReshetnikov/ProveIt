#!/usr/bin/env python3
"""Repair the old binder screen using the shared-helper-aware objective."""
from pathlib import Path
import json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import a10_source_search as a
s,z=a.s,a.z
objective=a.hw.make(a.table,a.old)[0]
path='1110100100111000010'
R=s.at(a.old,path) if hasattr(s,'at') else None
if R is None:
 R=a.old
 for bit in path:R=R[int(bit)]
I=z.MACRO[119]
from functools import cache
import itertools
@cache
def shapes(atoms):
 if len(atoms)==1:return (atoms[0],)
 return tuple((x,y)for k in range(1,len(atoms))for x in shapes(atoms[:k])for y in shapes(atoms[k:]))
@cache
def all_nodes(t):
 return frozenset({t}) if s.leaf(t) else frozenset({t})|all_nodes(t[0])|all_nodes(t[1])
res=[]
for swap,m,k in itertools.product((False,True),range(1,9),range(5)):
 if m==1 and k==0:continue
 if m>4 and k>1:continue
 push=R[0] if not swap else(R[0][1],R[0][0])
 for incs in shapes((('CI',1),)*m):
  loop=(('CD',7),(incs,('CC',2)))
  pair=(I[0],(I[1][0],loop))
  atoms=(push,pair)+((('CI',1),)*k)
  for binder in shapes(atoms):
   n=s.replace(a.old,path,binder)
   if len(all_nodes(n))>211:continue
   mm=s.metrics(n)
   if mm['maximum_zero_run']>7:continue
   res.append(dict(swap=swap,m=m,k=k,metrics=mm,hardware_lower_bound=objective(n)))
res2=[]
for p in sorted((Path(__file__).parent/'binders').glob('add_*/sites.json')):
 n=s.tree(json.loads(p.read_text()))
 res2.append(dict(name=p.parent.name,metrics=s.metrics(n),hardware_lower_bound=objective(n)))
out=dict(pair_cases=res,sum_cases=res2,minimum_pair_lower_bound=min(r['hardware_lower_bound']['cost_lower_bound']for r in res),minimum_sum_lower_bound=min(r['hardware_lower_bound']['cost_lower_bound']for r in res2))
(Path(__file__).parent/'binder_hardware_receipt.json').write_text(json.dumps(out,indent=2)+'\n')
print('cases',len(res),'pairbest',out['minimum_pair_lower_bound'],'sumbest',out['minimum_sum_lower_bound'])
print(json.dumps(res2,indent=2))
