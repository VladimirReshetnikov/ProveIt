#!/usr/bin/env python3
"""Exploratory context-free source DAG beam with exact graph verification."""
import argparse,json,random,time,functools,hashlib
from pathlib import Path
from model import *
from dag import Dag
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--seed',type=int,default=217);ap.add_argument('--width',type=int,default=100);ap.add_argument('--rounds',type=int,default=100);ap.add_argument('--seconds',type=int,default=300);ap.add_argument('--input',type=Path,default=BASE/'sites218.json');ap.add_argument('--affine',action='store_true');ap.add_argument('--disjoint',action='store_true');a=ap.parse_args()
a.output.mkdir(parents=True,exist_ok=True)
rr=json.loads(a.input.read_text());t=parse(rr);G=graph(rr);d=Dag();root=d.intern(t);mats={i:affine(d.tree(i))for i in range(len(d.ns))};rng=random.Random(a.seed)
seen={root};frontier=[root];parents={};best=len(d.reach(root));trials=0;start=time.monotonic();records=[];hits=[]
@functools.lru_cache(None)
def uses(q):
 n=d.ns[q]
 return ((1<<n[1]) if n[0]in('CI','CD')else 0,n[0]=='CH')if isinstance(n[0],str)else(uses(n[0])[0]|uses(n[1])[0],uses(n[0])[1]or uses(n[1])[1])
for depth in range(1,a.rounds+1):
 candidates=[]
 for r in frontier:
  for q in sorted(d.reach(r)):
   n=d.ns[q]
   if isinstance(n[0],str):continue
   x,y=n;opts=[]
   if a.affine and mats.get(x)is not None and mats.get(y)is not None and compose(mats[x],mats[y])==compose(mats[y],mats[x]):opts.append(('swap',d.add((y,x))))
   elif a.disjoint and d.br[x]==d.co[x]==d.br[y]==d.co[y]==0 and not(uses(x)[0]&uses(y)[0])and not uses(x)[1]and not uses(y)[1]:opts.append(('disjoint',d.add((y,x))))
   if not isinstance(d.ns[x][0],str):
    xx,xy=d.ns[x]
    if d.br[xx]==0 and d.co[y]==0:opts.append(('R',d.add((xx,d.add((xy,y))))))
   if not isinstance(d.ns[y][0],str):
    yx,yy=d.ns[y]
    if d.br[x]==0 and d.co[yy]==0:opts.append(('L',d.add((d.add((x,yx)),yy))))
   for kind,nq in opts:
    trials+=1
    if mats.get(q)is not None:mats[nq]=mats[q]
    nr=d.replace(r,q,nq)
    if nr in seen:continue
    seen.add(nr)
    if d.zero[nr]>6:continue
    reach=d.reach(nr);score=len(reach)
    if score>best+2:continue
    for z in reach:
     if z in mats:continue
     nn=d.ns[z]
     if not isinstance(nn[0],str) and mats.get(nn[0])is not None and mats.get(nn[1])is not None:mats[z]=compose(mats[nn[0]],mats[nn[1]])
    parents[nr]=(r,q,nq,kind);candidates.append((score,rng.random(),nr))
    if score<best:
     best=score;tt=d.tree(nr);rows=leaves(tt)
     assert graph(rows)==arithmetic_graph(rows)
     if not(a.affine or a.disjoint):assert graph(rows)==G
     chain=[];cur=nr
     while cur!=root:
      pr,oq,mq,di=parents[cur];chain.append({'kind':di,'old':d.tree(oq),'new':d.tree(mq)});cur=pr
     chain.reverse();hit={'score':score,'depth':depth,'sites':rows,'chain':chain,'trials':trials,'source':str(a.input),'seed':a.seed,'affine':a.affine,'disjoint':a.disjoint};hits.append(hit)
     (a.output/f'hit{score}.json').write_text(json.dumps(hit));print('BEST',score,'depth',depth,'trials',trials,flush=True)
 if not candidates:break
 candidates.sort();lowest=candidates[0][0]
 # Half best-cost, quarter next cost, quarter higher to escape plateaus.
 selected=[]
 for cost,limit in [(lowest,a.width//2),(lowest+1,a.width//4),(lowest+2,a.width//4)]:
  selected.extend([r for sc,_,r in candidates if sc==cost][:limit])
 selected+=([r for _,_,r in candidates if r not in set(selected)][:a.width-len(selected)])
 frontier=selected
 rec={'depth':depth,'candidates':len(candidates),'best':best,'current':lowest,'trials':trials,'interned':len(d.ns),'seconds':time.monotonic()-start};records.append(rec);print(json.dumps(rec),flush=True)
 if time.monotonic()-start>a.seconds or len(d.ns)>6000000 or best<204:break
(a.output/'result.json').write_text(json.dumps({'best':best,'seed':a.seed,'affine':a.affine,'records':records,'hits':hits},indent=2))
