#!/usr/bin/env python3
"""Signed-row formulas in the inherited closed-atom skeleton, without row boxes."""
import itertools,json,time
from pathlib import Path
from functools import cache
ns={'__name__':'signed_support'}
src=Path(__file__).with_name('disequality_signed219.py').read_text()
exec(src[:src.index('\nresults=[];best=999')],ns)
globals().update(ns)
RAW=s.tree(json.loads((q.W/'disequality_codec219/raw/sites.json').read_text()))
OUT=q.W/'disequality_signed_atoms219';OUT.mkdir(exist_ok=True)
@cache
def atoms(n):
 if not s.leaf(n)and s.boundary(n[0])==s.boundary(n[1])==(0,0,False):return atoms(n[0])+atoms(n[1])
 assert s.boundary(n)==(0,0,False)
 return(n,)
intervals={'G':(486,1036),'rho5':(1319,1662),'rho3':(1961,2304)}
oldatoms={k:[]for k in intervals}
def template(n,i=0):
 j=i+len(q.x.flat(n))
 for name,(lo,hi)in intervals.items():
  if lo<=i and j<=hi and s.boundary(n)==(0,0,False):
   if s.leaf(n)or any(s.boundary(ch)!=(0,0,False)for ch in n):
    k=len(oldatoms[name]);oldatoms[name].append(n);return('A',name,k)
 if all(j<=lo or i>=hi for lo,hi in intervals.values()):return('F',n)
 return('N',template(n[0],i),template(n[1],i+len(q.x.flat(n[0]))))
SK=template(RAW)
for name,(lo,hi)in intervals.items():assert sum((q.x.flat(a)for a in oldatoms[name]),())==q.x.flat(RAW)[lo:hi]
def compose(t,newatoms):
 if t[0]=='F':return t[1]
 if t[0]=='A':return newatoms[t[1]][t[2]]
 return compose(t[1],newatoms),compose(t[2],newatoms)
def simplify(n):
 cursor=0
 def go(t):
  nonlocal cursor
  if s.leaf(t):
   i=cursor;cursor+=1;return None if 2762<=i<2856 else t
  a,bb=go(t[0]),go(t[1]);return bb if a is None else a if bb is None else(a,bb)
 return go(n)
results=[];best=999;start=time.time()
for gi,ri,si in itertools.product(range(5),range(3),range(3)):
 words={'G':emit(gs[gi]),'rho3':emit(rhs3[ri]),'rho5':emit(rhs5[si])}
 newatoms={name:sum((atoms(z.MACRO[m])for m in word),())for name,word in words.items()}
 assert {k:len(v)for k,v in newatoms.items()}=={k:len(v)for k,v in oldatoms.items()}
 tr=compose(SK,newatoms)
 for simple,eswap in itertools.product([False,True],repeat=2):
  tt=simplify(tr)if simple else tr
  if eswap:tt=eqswap(tt)
  metric=s.metrics(tt);name=f'g{gi}_r3{ri}_r5{si}_simple{int(simple)}_eswap{int(eswap)}'
  rec={'name':name,'words':words,'simplified_rho1':simple,'swap_equality_counters':eswap,'metrics':metric}
  if metric['dag_nodes']<best:best=metric['dag_nodes'];print('BEST',best,name,flush=True)
  if metric['dag_nodes']<=210:
   dd=OUT/name;dd.mkdir(exist_ok=True);rr=s.sites(tt);assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
   (dd/'sites.json').write_bytes(s.compact(rr))
   try:
    U,meta=compiler.compile_tree(T,OLD,tt,extend_direct=True);rec['compiler']=meta;(dd/'candidate.tm').write_bytes(b.table_bytes(U))
   except Exception as exc:rec['error']=repr(exc)
   (dd/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
  results.append(rec)
(OUT/'summary.json').write_text(json.dumps({'tested':len(results),'minimum_DAG':best,'results':results,'seconds':time.time()-start,'closed_atom_counts':{k:len(v)for k,v in oldatoms.items()}},indent=2)+'\n')
