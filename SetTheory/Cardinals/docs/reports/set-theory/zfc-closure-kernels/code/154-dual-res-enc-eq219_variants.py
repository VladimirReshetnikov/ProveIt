#!/usr/bin/env python3
"""Compile all archived clean-equality source trees against K219."""
from pathlib import Path
from functools import cache
import itertools,json
import inverse_mp as q
import recompile219 as compiler
s,b,z=q.s,q.b,q.z
BASE=q.W/'K219_Construction_2026-10-20'
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
old=s.tree(json.loads((BASE/'machine/sites219.json').read_text()))
OUT=q.W/'eq219_variants';OUT.mkdir(exist_ok=True)
def tup(n):return tuple(tup(a)if isinstance(a,list)else a for a in n)
hits=[tup(n)for n in json.loads((BASE/'research/encoding/eq_clean_hits.json').read_text())]
OLD=hits[10]
assert s.subtree(old,'111110')==OLD

def change(n,new):
 if n==OLD:return new
 if s.leaf(n):return n
 return change(n[0],new),change(n[1],new)

results=[]
for k,n in enumerate(hits):
 tt=change(old,n);rr=s.sites(tt)
 assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
 rec={'hit':k,'metrics':s.metrics(tt),'status':'Finite-calibrated search hit; full comparator proof available only for archivedhit10 unless separately supplied'}
 d=OUT/f'hit{k}';d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(s.compact(rr))
 try:
  U,c=compiler.compile_tree(T,old,tt);rec['compiler']=c;(d/'candidate.tm').write_bytes(b.table_bytes(U))
 except Exception as exc:rec['error']=repr(exc)
 (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');results.append(rec);print(json.dumps(rec),flush=True)
(OUT/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
