#!/usr/bin/env python3
"""Calibrated-formalism source experiments: negative equality and dual B.

Only the full translated rho1 and unchanged R1/J3 meanings currently have
an equiconsistency argument. Counts below are exploratory decoder counts.
"""
import json,itertools,time
from pathlib import Path
from functools import cache
import inverse_mp as q
import recompile219 as compiler
s,b,z=q.s,q.b,q.z
BASE=q.W/'K219_Construction_2026-10-20'
ROWS=json.loads((BASE/'machine/sites219.json').read_text());OLD=s.tree(ROWS)
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
OUT=q.W/'disequality_dual219';OUT.mkdir(exist_ok=True)
@cache
def flat(n):return (n,)if s.leaf(n)else flat(n[0])+flat(n[1])
@cache
def atoms(n):
 if not s.leaf(n)and s.boundary(n[0])==s.boundary(n[1])==(0,0,False):return atoms(n[0])+atoms(n[1])
 assert s.boundary(n)==(0,0,False)
 return(n,)
lo,hi=895,1178
NEWWORD=[168,166,166,168,183,180,119]
newatoms=sum((atoms(z.MACRO[m])for m in NEWWORD),())
oldatoms=[]
def template(n,i=0):
 j=i+len(flat(n))
 if j<=lo or i>=hi:return('F',n)
 if lo<=i and j<=hi and s.boundary(n)==(0,0,False):
  if s.leaf(n)or any(s.boundary(ch)!=(0,0,False)for ch in n):
   k=len(oldatoms);oldatoms.append(n);return('A',k)
 return('N',template(n[0],i),template(n[1],i+len(flat(n[0]))))
tpl=template(OLD);assert len(oldatoms)==len(newatoms)
assert sum((flat(a)for a in oldatoms),())==flat(OLD)[lo:hi]
def compose(t):
 if t[0]=='F':return t[1]
 if t[0]=='A':return newatoms[t[1]]
 return(compose(t[1]),compose(t[2]))
B=compose(tpl)
assert flat(B)==flat(OLD)[:lo]+sum((flat(z.MACRO[m])for m in NEWWORD),())+flat(OLD)[hi:]
ends={v+29 for v in[538,620,782,1230,1825,2497]};NEG=z.MACRO[218]
cursor=0
def change(n):
 global cursor
 if s.leaf(n):
  i=cursor;cursor+=1
  return(n,NEG)if i in ends else n
 return change(n[0]),change(n[1])
raw=change(B);assert cursor==4744
NP='1110100101';nn=s.subtree(raw,NP)
odd=(('CD',5),((('CD',5),('CC',2)),('CH',None)))
raw=s.replace(raw,NP,(odd,nn[1][1]))
E=s.subtree(OLD,'111110')
def tup(n):return tuple(tup(a)if isinstance(a,list)else a for a in n)
hits=[tup(n)for n in json.loads((BASE/'research/encoding/eq_clean_hits.json').read_text())]
def rename(n):
 if s.leaf(n):
  op,a=n;return(op,11-a)if op in('CI','CD')and a in(5,6)else n
 return rename(n[0]),rename(n[1])
def replace(n,e):
 if n==E:return e
 if s.leaf(n):return n
 return replace(n[0],e),replace(n[1],e)
def save(name,tr,metadata=None):
 rr=s.sites(tr);assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
 rec={'name':name,'metrics':s.metrics(tr),'status':'EXPLORATORY_SOURCE_AND_DECODER_ONLY',**(metadata or{})}
 dd=OUT/name;dd.mkdir(exist_ok=True);(dd/'sites.json').write_bytes(s.compact(rr))
 try:
  U,meta=compiler.compile_tree(T,OLD,tr,extend_direct=True);rec['compiler']=meta;(dd/'candidate.tm').write_bytes(b.table_bytes(U))
 except Exception as exc:rec['error']=repr(exc)
 (dd/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True);return rec
results=[save('raw_B',raw,{'equiconsistency_scope':'Full rho1, R1/J3, derived equality NJ; source implementation and runtime must still be certified.'})]
for k in [10]+[i for i in range(16)if i!=10]:
 for swap in[False,True]:
  tr=replace(raw,rename(hits[k])if swap else hits[k]);rec={'name':f'eq{k}'+('_swap'if swap else''),'metrics':s.metrics(tr)}
  if rec['metrics']['dag_nodes']<=210:rec=save(rec['name'],tr)
  else:print(json.dumps(rec),flush=True)
  results.append(rec)
(OUT/'summary.json').write_text(json.dumps({'rho6_word':NEWWORD,'closed_atoms':len(newatoms),'results':results},indent=2)+'\n')
