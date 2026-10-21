#!/usr/bin/env python3
"""Reparse the full axiom prefix using a fixed reference grammar only."""
from pathlib import Path
import itertools,json,time
import inverse_mp as q
import recompile219 as compiler
import closed_parse as cp
s,b,z=q.s,q.b,q.z
BASE=q.W/'K219_Construction_2026-10-20'
OLD=s.tree(json.loads((BASE/'machine/sites219.json').read_text()))
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
RAW=s.tree(json.loads((q.W/'disequality_codec219/raw/sites.json').read_text()))
OUT=q.W/'disequality_strict_parse219';OUT.mkdir(exist_ok=True)
p='111010010011';n=s.subtree(RAW,p)
assert s.boundary(n[0])==(0,0,False)and s.boundary(n[1][0])==(0,0,False)
tree=s.replace(RAW,p,((n[0],n[1][0]),n[1][1]))
assert s.graph_intervals(s.sites(tree))==s.graph_intervals(s.sites(RAW))
reference={'old':OLD,'derived_equality':(OLD,(z.MACRO[182],z.MACRO[218]))}
results=[];start=time.time();best=999
for refname,seed in itertools.product(reference,range(4)):
 tr,parse=cp.parse_one(tree,reference[refname],p+'0',6,seed,reference_only=True)
 rr=s.sites(tr);assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)==s.graph_intervals(s.sites(RAW))
 rec={'reference':refname,'seed':seed,'metrics':s.metrics(tr),'parse':parse}
 if rec['metrics']['dag_nodes']<=211:
  d=OUT/f'{refname}_seed{seed}';d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(s.compact(rr))
  try:
   U,meta=compiler.compile_tree(T,OLD,tr,extend_direct=True);rec['compiler']=meta
   (d/'candidate.tm').write_bytes(b.table_bytes(U))
  except Exception as exc:rec['error']=repr(exc)
  (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
 print(json.dumps(rec),flush=True);results.append(rec)
(OUT/'summary.json').write_text(json.dumps({'results':results,'seconds':time.time()-start},indent=2)+'\n')
