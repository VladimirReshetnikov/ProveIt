#!/usr/bin/env python3
"""Apply previously justified source variations to the new K219 comparator baseline."""
from pathlib import Path
import itertools,json
import inverse_mp as q
s,b,z=q.s,q.b,q.z
import recompile219 as compiler
BASE=q.W/'K219_Construction_2026-10-20'
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
ROWS=json.loads((BASE/'machine/sites219.json').read_text());old=s.tree(ROWS)
OUT=q.W/'rebase219';OUT.mkdir(exist_ok=True)
move=lambda i,j:(('CD',i),(('CI',j),('CC',2)))
assert q.x.flat(s.subtree(old,'111111'))==q.x.flat(z.MACRO[166])
variants={'original':old,'no_push_copy':s.replace(old,'111111',z.MACRO[166][1]),'no_push_move':s.replace(old,'111111',move(4,1)),'no_push_cache':s.replace(old,'111111',move(4,5))}
for name,tt in list(variants.items()):
 rr=s.sites(tt)
 for i in range(895,1178):
  if rr[i][1]in('CI','CD'):rr[i][2]={3:5,5:3}.get(rr[i][2],rr[i][2])
 variants[name+'_rho6swap']=s.tree(rr)
results=[]
for name,new in variants.items():
 rr=s.sites(new);assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
 rec={'variant':name,'metrics':s.metrics(new),'status':'EXPLORATORY_COMPILER_COUNT; changed source and startup/runtime require separate validation'}
 d=OUT/name;d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(s.compact(rr))
 try:
  U,c=compiler.compile_tree(T,old,new);rec['compiler']=c;(d/'candidate.tm').write_bytes(b.table_bytes(U))
 except Exception as exc:rec['error']=repr(exc)
 (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');results.append(rec);print(json.dumps(rec),flush=True)
(OUT/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
