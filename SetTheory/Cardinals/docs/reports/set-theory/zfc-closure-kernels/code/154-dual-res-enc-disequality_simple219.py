#!/usr/bin/env python3
"""Simplify rho1's double negation and vary equality counter orientation."""
import json
from pathlib import Path
import inverse_mp as q
import recompile219 as compiler
s,b=q.s,q.b
BASE=q.W/'K219_Construction_2026-10-20'
OLD=s.tree(json.loads((BASE/'machine/sites219.json').read_text()))
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
RAW=s.tree(json.loads((q.W/'disequality_codec219/raw/sites.json').read_text()))
OUT=q.W/'disequality_simple219';OUT.mkdir(exist_ok=True)
lo,hi=2762,2856
rawrows=s.sites(RAW)
assert tuple(tuple(r[1:])for r in rawrows[lo:hi])==q.x.flat(q.z.MACRO[218])*2
cursor=0
def delete(n):
 global cursor
 if s.leaf(n):
  i=cursor;cursor+=1
  return None if lo<=i<hi else n
 a,bb=delete(n[0]),delete(n[1])
 return bb if a is None else a if bb is None else(a,bb)
simple=delete(RAW)
oldg=s.graph_intervals(rawrows)
kept=[i for i in range(len(rawrows))if not lo<=i<hi]
mapped={i:j for j,i in enumerate(kept)}
def target(i):return mapped[hi]if lo<=i<hi else mapped[i]
expected=[[effect,[target(t)for t in targets]]for i,(effect,targets)in enumerate(oldg)if i in mapped]
assert s.graph_intervals(s.sites(simple))==expected,'Contraction changed an external control edge'

def rename(n):
 if s.leaf(n):
  op,arg=n
  return(op,11-arg)if op in('CI','CD')and arg in(5,6)else n
 return rename(n[0]),rename(n[1])
E=s.subtree(OLD,'111110')
def replace(n,e):
 if n==E:return e
 if s.leaf(n):return n
 return replace(n[0],e),replace(n[1],e)
def tup(n):return tuple(tup(a)if isinstance(a,list)else a for a in n)
hits=[tup(n)for n in json.loads((BASE/'research/encoding/eq_clean_hits.json').read_text())]
results=[]
for base,tree in [('raw',RAW),('rho1_simple',simple)]:
 for k in [10]+[i for i in range(16)if i!=10]:
  for swap in [False,True]:
   hit=rename(hits[k])if swap else hits[k]
   tr=replace(tree,hit);metric=s.metrics(tr)
   name=f'{base}_eq{k}'+('_swap'if swap else'')
   rec={'name':name,'metrics':metric,'rho1_contraction_CFG_preserved':True}
   if metric['dag_nodes']<=209:
    dd=OUT/name;dd.mkdir(exist_ok=True);(dd/'sites.json').write_bytes(s.compact(s.sites(tr)))
    try:
     U,meta=compiler.compile_tree(T,OLD,tr,extend_direct=True);rec['compiler']=meta
     (dd/'candidate.tm').write_bytes(b.table_bytes(U))
    except Exception as exc:rec['error']=repr(exc)
    (dd/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
   results.append(rec);print(json.dumps(rec),flush=True)
(OUT/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
