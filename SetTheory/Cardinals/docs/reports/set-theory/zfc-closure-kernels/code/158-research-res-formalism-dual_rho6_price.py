#!/usr/bin/env python3
"""Exhaustive Catalan pricing of rho6 and its classical dual, six field orders."""
from pathlib import Path
import os
import sys,json,itertools,time
from functools import cache
HERE=Path(__file__).resolve().parent;Z=Path(os.environ.get('PROVEIT_ZFC_ROOT', str(HERE.parent/'ProveIt/Computability/BusyBeaver/Research/ZFC'))).resolve();sys.path.insert(0,str(Z/'k218-quantifier-stability/pricing'))
import source_language as s,build221 as b,measure_pinned as m
root=s.tree(json.loads((Z/'candidate-k218/sites218.json').read_text()));tab=b.read_table((Z/'candidate-k218/k218.native.tm').read_bytes());g,_=b.decoder_map(tab,root);q=lambda k:b.sole(g,k)
macros={'a':q(98),'b':q(12),'c':q(166),'I':q(90),'Q':q(86),'F':q(184)[0]};hole=('HOLE',0);ctx=m.splice(s,root,895,1178,hole)
out=HERE/'dual-rho6-price';out.mkdir(exist_ok=True);records=[];best=999;best6=999;started=time.monotonic();total=0
# Fixed baseline node numbering with metrics and reachability masks.
bnodes=[];bid={}
def base(t):
 if t in bid:return bid[t]
 if not s.leaf(t):base(t[0]);base(t[1])
 i=len(bnodes);bid[t]=i;bnodes.append(t);return i
base(root)
def context_base(t):
 if t==hole:return True
 if s.leaf(t):base(t);return False
 a=context_base(t[0]);bb=context_base(t[1])
 if not(a or bb):base(t)
 return a or bb
context_base(ctx);B=len(bnodes)
@cache
def bnmask(i):
 t=bnodes[i];return(1<<i)if s.leaf(t)else(1<<i)|bnmask(bid[t[0]])|bnmask(bid[t[1]])
@cache
def met(t):
 if s.leaf(t):return 0,0,0 # leading zeros, maximum zeros, depth
 a,bb=met(t[0]),met(t[1]);return a[0]+1,max(a[0]+1,a[1],bb[1]),1+max(a[2],bb[2])
def context(t):
 if t==hole:return 0,[]
 if t in bid:return bnmask(bid[t]),None
 a,pa=context(t[0]);bb,pb=context(t[1])
 assert(pa is None)!=(pb is None)
 return a|bb,([(0,t[1])]+pa if pa is not None else[(1,t[0])]+pb)
cmask,path=context(ctx);H=len(path)
for kind in('old','dual'):
 for v,w in itertools.permutations('abc',2):
  word=(v,v,w,'Q','F','I','Q','F','I',w,'I')if kind=='old'else(w,v,v,w,'F','I','Q','F','I','Q','I')
  pairs={};trees=list(bnodes);masks=[bnmask(i)for i in range(B)];fresh=[frozenset()for _ in range(B)];mets=[met(t)for t in bnodes]
  for i,t in enumerate(bnodes):
   if not s.leaf(t):pairs[bid[t[0]],bid[t[1]]]=i
  def node(a,bb):
   key=(a,bb)
   if key in pairs:return pairs[key]
   i=len(trees);pairs[key]=i;trees.append((trees[a],trees[bb]));masks.append(masks[a]|masks[bb]);fresh.append(fresh[a]|fresh[bb]|{i});x,y=mets[a],mets[bb];mets.append((x[0]+1,max(x[0]+1,x[1],y[1]),1+max(x[2],y[2])));return i
  @cache
  def spans(lo,hi):
   if hi-lo==1:return[bid[macros[word[lo]]]]
   return[node(a,bb)for k in range(lo+1,hi)for a in spans(lo,k)for bb in spans(k,hi)]
  roots=spans(0,len(word));count=0;localbest=999;localbest6=999;keep=[]
  for i in roots:
   total+=1;count+=1;x=mets[i]
   for side,sib in reversed(path):
    y=met(sib);a,bb=(x,y)if side==0 else(y,x);x=(a[0]+1,max(a[0]+1,a[1],bb[1]),1+max(a[2],bb[2]))
   score=(cmask|masks[i]).bit_count()+len(fresh[i])+H
   if i<B:
    t=m.splice(s,root,895,1178,trees[i]);actual=s.metrics(t);score=actual['dag_nodes']
   localbest=min(localbest,score)
   if x[1]<=6:localbest6=min(localbest6,score)
   if score<best or(x[1]<=6 and score<best6):
    t=m.splice(s,root,895,1178,trees[i]);rr=s.sites(t);actual=s.metrics(t);assert actual['dag_nodes']==score,(actual,score);assert actual['maximum_zero_run']==x[1]
    assert s.graph_intervals(rr)==s.graph_arithmetic(rr)[0]
    rec=dict(kind=kind,binder=v,matrix=w,word=word,trial=total,metrics=actual,scope='Closed source splice; dual rho6 has ordinary classical equivalence. No allocator/runtime/startup.')
    d=out/f'candidate{total:06d}';d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(s.compact(rr));(d/'result.json').write_text(json.dumps(rec,indent=2));print('BEST',rec,round(time.monotonic()-started,3),flush=True)
    best=min(best,score)
    if x[1]<=6:best6=min(best6,score)
  rec=dict(kind=kind,binder=v,matrix=w,count=count,best=localbest,best6=localbest6,new_nodes=len(trees)-B,seconds=round(time.monotonic()-started,3));records.append(rec);print('FAMILY',rec,flush=True)
  spans.cache_clear()
(out/'result.json').write_text(json.dumps(dict(trials=total,best=best,best6=best6,records=records),indent=2));print('DONE',total,best,best6,flush=True)
