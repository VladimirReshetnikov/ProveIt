#!/usr/bin/env python3
"""Price freshness-by-construction bundle wrapper plus ungated cleanup."""
from pathlib import Path
import os
import sys,json,itertools,collections,time
from functools import cache
HERE=Path(__file__).resolve().parent;Z=Path(os.environ.get('PROVEIT_ZFC_ROOT', str(HERE.parent/'ProveIt/Computability/BusyBeaver/Research/ZFC'))).resolve()
sys.path.insert(0,str(Z/'k218-quantifier-stability/pricing'))
import source_language as s,build221 as b,measure_pinned as m
r=s.tree(json.loads((Z/'candidate-k218/sites218.json').read_text()));tab=b.read_table((Z/'candidate-k218/k218.native.tm').read_bytes());g,_=b.decoder_map(tab,r);q=lambda k:b.sole(g,k)
macros={'a':q(98),'b':q(12),'c':q(166),'I':q(90),'Q':q(86)}
@cache
def shapes(ts):
 if len(ts)==1:return[ts[0]]
 return[(a,bb)for k in range(1,len(ts))for a in shapes(ts[:k])for bb in shapes(ts[k:])]
clears={k:(('CD',k),('CC',1))for k in(3,4,5)}
for c in clears.values():assert s.boundary(c)==(0,0,False)
root=HERE/'wrapper-price';root.mkdir(exist_ok=True);best=999;records=[];trial=0;started=time.monotonic()
for order in itertools.permutations((3,4,5)):
 for cleart in shapes(tuple(clears[k]for k in order)):
  base=m.splice(s,r,4563,4597,cleart)
  for word in [('a','b','Q','c','I'),('b','a','Q','c','I'),('a','b','I','c','Q'),('b','a','I','c','Q')]:
   for wi,wrapper in enumerate(shapes(tuple(macros[x]for x in word))):
    assert s.boundary(wrapper)==(0,0,False)
    seen=[]
    def mutate(t,k=0):
     nn=len(s.sites(t))
     if 2650<=k and k+nn<=4563 and t==macros['c']:seen.append(k);return wrapper
     if s.leaf(t):return t
     return mutate(t[0],k),mutate(t[1],k+len(s.sites(t[0])))
    t=mutate(base);trial+=1;assert len(seen)==13,(len(seen),seen)
    met=s.metrics(t);info=dict(trial=trial,clear_order=order,clear_tree=cleart,wrapper_word=word,wrapper_shape=wi,metrics=met,substituted_old_ordinals=seen)
    if met['dag_nodes']<=best:
     best=met['dag_nodes'];out=root/f'candidate{trial:04d}';out.mkdir(exist_ok=True);rr=s.sites(t);assert s.graph_intervals(rr)==s.graph_arithmetic(rr)[0]
     (out/'sites.json').write_bytes(s.compact(rr));(out/'result.json').write_text(json.dumps(info,indent=2));info['path']=str(out)
     print('BEST',trial,met,word,order,'shape',wi,round(time.monotonic()-started,3),flush=True)
    records.append(info)
(root/'result.json').write_text(json.dumps(dict(trials=trial,best_dag=best,records=records),indent=2));print('DONE',trial,best,round(time.monotonic()-started,3),flush=True)
