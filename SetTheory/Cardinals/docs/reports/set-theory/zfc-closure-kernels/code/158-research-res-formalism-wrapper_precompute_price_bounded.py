#!/usr/bin/env python3
from pathlib import Path
import os
import sys,json,itertools,time
from functools import cache
HERE=Path(__file__).resolve().parent;Z=Path(os.environ.get('PROVEIT_ZFC_ROOT', str(HERE.parent/'ProveIt/Computability/BusyBeaver/Research/ZFC'))).resolve();sys.path.insert(0,str(Z/'k218-quantifier-stability/pricing'))
import source_language as s,build221 as b,measure_pinned as m
r=s.tree(json.loads((Z/'candidate-k218/sites218.json').read_text()));tab=b.read_table((Z/'candidate-k218/k218.native.tm').read_bytes());g,_=b.decoder_map(tab,r);q=lambda k:b.sole(g,k)
macros={'a':q(98),'b':q(12),'c':q(166),'I':q(90),'Q':q(86),'clr3':(('CD',3),('CC',1)),'to3':(('CD',1),(('CI',3),('CC',2))),'unpair':q(105),'to1':q(81)}
for k,t in macros.items():assert s.boundary(t)==(0,0,False),k
@cache
def shapes(ts):
 if len(ts)==1:return[ts[0]]
 return[(a,bb)for k in range(1,len(ts))for a in shapes(ts[:k])for bb in shapes(ts[k:])]
@cache
def nodes(t):
 return frozenset([t])if s.leaf(t)else frozenset([t])|nodes(t[0])|nodes(t[1])
clears={k:(('CD',k),('CC',1))for k in(3,4,5)}
root=HERE/'wrapper-precompute-price-bounded';root.mkdir(exist_ok=True);best=999;records=[];trial=0;started=time.monotonic()
for order in itertools.permutations((3,4,5)):
 for ci,cleart in enumerate(shapes(tuple(clears[k]for k in order))):
  base=m.splice(s,r,4563,4597,cleart);bn=nodes(base)
  for word in [('a','b','Q','c','I'),('b','a','Q','c','I'),('a','b','I','c','Q'),('b','a','I','c','Q')]:
   prefword=word+('clr3','to3','unpair','to1');ps=shapes(tuple(macros[x]for x in prefword));costs=[(len(nodes(t)-bn),i,t)for i,t in enumerate(ps)];mc=min(c for c,_,t in costs)
   costs=[z for z in costs if z[0]==mc][:3]
   for pc,pi,prefix in costs:
    seen=[]
    def mutate(t,k=0):
     if k==2650 and t==macros['a']:seen.append(k);return prefix,t
     if s.leaf(t):return t
     return mutate(t[0],k),mutate(t[1],k+len(s.sites(t[0])))
    t=mutate(base);trial+=1;assert seen==[2650]
    met=s.metrics(t);info=dict(trial=trial,clear_order=order,clear_shape=ci,wrapper_word=word,prefix_shape=pi,prefix_newnodes=pc,metrics=met)
    if met['dag_nodes']<=best:
     best=met['dag_nodes'];out=root/f'candidate{trial:05d}';out.mkdir(exist_ok=True);rr=s.sites(t);assert s.graph_intervals(rr)==s.graph_arithmetic(rr)[0]
     (out/'sites.json').write_bytes(s.compact(rr));(out/'result.json').write_text(json.dumps(info,indent=2));info['path']=str(out);print('BEST',trial,met,word,order,'shape',pi,round(time.monotonic()-started,3),flush=True)
    records.append(info)
(root/'result.json').write_text(json.dumps(dict(trials=trial,best_dag=best,records=records),indent=2));print('DONE',trial,best,round(time.monotonic()-started,3),flush=True)
