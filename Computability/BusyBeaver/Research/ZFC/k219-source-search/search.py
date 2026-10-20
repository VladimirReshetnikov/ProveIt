#!/usr/bin/env python3
"""Bounded global DAG walk using proved open association and affine commutation.

The 30-wide beam is incomplete; costs207 may be selected in affine mode.
No binary compiler is run and no state-count conclusion follows.
"""
import argparse,json,functools,random,time,collections,hashlib
from pathlib import Path
from model import *
from dag import Dag
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output',type=Path,required=True)
ap.add_argument('--affine',action='store_true')
ap.add_argument('--rounds',type=int,default=30)
ap.add_argument('--seed',type=int,default=219206)
args=ap.parse_args();assert 1<=args.rounds<=30 and __debug__
args.output.mkdir(parents=True,exist_ok=False)
tree,rows=load();G=graph(rows)
d=Dag();root=d.intern(tree);mats={i:affine(d.tree(i)) for i in range(len(d.ns))};rng=random.Random(args.seed);seen={root};frontier=[root];parents={};best=206;trials=0;accepted=0;started=time.monotonic();levels=[];hits=[]
for depth in range(1,args.rounds+1):
 candidates=[]
 for rr in frontier:
  for q in sorted(d.reach(rr)):
   n=d.ns[q]
   if isinstance(n[0],str):continue
   a,b=n;opts=[]
   ma=mats.get(a);mb=mats.get(b)
   if args.affine and ma is not None and mb is not None and compose(ma,mb)==compose(mb,ma):opts.append(('swap',d.add((b,a))))
   if not isinstance(d.ns[a][0],str):
    aa,ab=d.ns[a]
    if d.br[aa]==0 and d.co[b]==0:opts.append(('R',d.add((aa,d.add((ab,b))))))
   if not isinstance(d.ns[b][0],str):
    ba,bb=d.ns[b]
    if d.br[a]==0 and d.co[bb]==0:opts.append(('L',d.add((d.add((a,ba)),bb))))
   for kind,nq in opts:
    trials+=1
    if mats.get(q) is not None:mats[nq]=mats[q]
    nr=d.replace(rr,q,nq)
    for qq in d.reach(nr):
     if qq in mats:continue
     nn=d.ns[qq]
     if not isinstance(nn[0],str) and mats.get(nn[0]) is not None and mats.get(nn[1]) is not None:mats[qq]=compose(mats[nn[0]],mats[nn[1]])
    if nr in seen:continue
    seen.add(nr)
    if d.zero[nr]>6:continue
    score=len(d.reach(nr))
    if score>207:continue
    accepted+=1;parents[nr]=(rr,q,nq,kind);candidates.append((score,rng.random(),nr))
    if score<best:
     best=score;t=d.tree(nr);assert metrics(t)['dag_nodes']==score
     if not args.affine:assert graph(leaves(t))==G
     chain=[];cur=nr
     while cur!=root:
      pr,oq,mq,di=parents[cur];chain.append({'direction':di,'old':d.tree(oq),'new':d.tree(mq)});cur=pr
     chain.reverse();h={'score':score,'depth':depth,'sites':leaves(t),'chain':chain,'trials':trials};hits.append(h)
     (args.output/'best.json').write_text(json.dumps(h));print('BEST',score,'depth',depth,'trials',trials,flush=True)
 if not candidates:break
 candidates.sort()
 if args.affine:
  near=[c for c in candidates if c[0]==207];frontier=[r for _,_,r in candidates[:15]]+[r for _,_,r in near[:15]]
  if len(frontier)<30:frontier=[r for _,_,r in candidates[:30]]
 else:frontier=[r for _,_,r in candidates[:30]]
 levels.append({'depth':depth,'candidates':len(candidates),'best':candidates[0][0],'trials':trials,'interned':len(d.ns),'elapsed':time.monotonic()-started})
 print(levels[-1],flush=True)
 if time.monotonic()-started>120 or len(d.ns)>3000000:break
res={'scope':('seeded beam15 best +15 cost207, with commuting affine swaps' if args.affine else 'seeded beam30 best-cost open-safe rotations')+'; DAG<=207/maxzero6; not exhaustive','best':best,'trials':trials,'accepted':accepted,'unique_roots':len(seen),'levels':levels,'hits':hits,'seconds':time.monotonic()-started}
res.update(affine=args.affine,seed=args.seed,requested_rounds=args.rounds,completed_rounds=len(levels),input_sha256=hashlib.sha256((BASE/'sites219.json').read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(args.output/'result.json').write_text(json.dumps(res,indent=2)+'\n')
