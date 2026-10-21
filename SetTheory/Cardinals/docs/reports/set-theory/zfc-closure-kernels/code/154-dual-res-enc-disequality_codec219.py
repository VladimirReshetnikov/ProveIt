#!/usr/bin/env python3
"""Source sharing for a raw disequality tag and derived equality N(J).

Logical calibration is supplied separately. Table counts do not certify runtime.
"""
from pathlib import Path
from functools import cache
import itertools,json,time
import inverse_mp as q
import recompile219 as compiler
import closed_parse as cp
from semantic_grammar import atoms,dag
s,b,z=q.s,q.b,q.z
BASE=q.W/'K219_Construction_2026-10-20'
OLDROWS=json.loads((BASE/'machine/sites219.json').read_text());OLD=s.tree(OLDROWS)
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
OUT=q.W/'disequality_codec219';OUT.mkdir(exist_ok=True)
starts=[538,620,782,1230,1825,2497]
ends={lo+29 for lo in starts}
NEG=z.MACRO[218]
assert all(tuple(tuple(r[1:])for r in OLDROWS[lo:lo+30])==q.x.flat(z.MACRO[182])for lo in starts)
assert s.boundary(NEG)==(0,0,False)
cursor=0
def change(n):
 global cursor
 if s.leaf(n):
  i=cursor;cursor+=1
  return(n,NEG)if i in ends else n
 return change(n[0]),change(n[1])
raw=change(OLD);assert cursor==len(OLDROWS)
NP='1110100101';nn=s.subtree(raw,NP)
assert nn[0]==('CI',6)and nn[1][0][1]==('CH',None)
odd=(('CD',5),((('CD',5),('CC',2)),('CH',None)))
raw=s.replace(raw,NP,(odd,nn[1][1]))
reference=(OLD,(z.MACRO[182],NEG))
paths=['111010010011011111','1110100100111000011',
       '1110100100111001001','1110100100111010000100111',
       '111010010011101000101111']

def save(name,tree,extra=None):
 rr=s.sites(tree);assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
 rec={'name':name,'metrics':s.metrics(tree),'status':'EXPLORATORY_SOURCE_AND_DECODER_ONLY',**(extra or{})}
 d=OUT/name;d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(s.compact(rr))
 try:
  U,meta=compiler.compile_tree(T,OLD,tree,extend_direct=True);rec['compiler']=meta
  (d/'candidate.tm').write_bytes(b.table_bytes(U))
 except Exception as exc:rec['error']=repr(exc)
 (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True)
 return rec

results=[save('raw',raw)]
best=999
for seed in range(12):
 tr=raw;changes=[]
 for p in paths:
  tr,rec=cp.parse_one(tr,reference,p,6,seed);changes.append(rec)
 stats=s.metrics(tr)
 if stats['dag_nodes']<best:
  best=stats['dag_nodes'];results.append(save(f'reparse_seed{seed}',tr,{'reparses':changes}))
(OUT/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
