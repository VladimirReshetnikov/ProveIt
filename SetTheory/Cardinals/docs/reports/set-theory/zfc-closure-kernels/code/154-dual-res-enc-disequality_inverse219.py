#!/usr/bin/env python3
"""Combine old-rho6 negative equality, parity halting, and inverse detachment.

Counts are exploratory; the changed primitive entries have no runtime certificate.
The 11-leaf loop is explicitly tested and rejected under the unchanged codec.
"""
from pathlib import Path
import json
import inverse_mp as q
import recompile219 as compiler

s,b,z=q.s,q.b,q.z
BASE=q.W/'K219_Construction_2026-10-20'
OLDROWS=json.loads((BASE/'machine/sites219.json').read_text());OLD=s.tree(OLDROWS)
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
OUT=q.W/'disequality_inverse219';OUT.mkdir(exist_ok=True)
ends={p+29 for p in (538,620,782,1230,1825,2497)}
cursor=0
def translate(n):
 global cursor
 if s.leaf(n):
  i=cursor;cursor+=1
  return (n,z.MACRO[218]) if i in ends else n
 return translate(n[0]),translate(n[1])
raw=translate(OLD)
np='1110100101';nn=s.subtree(raw,np)
odd=(q.CD(5),((q.CD(5),q.CC(2)),('CH',None)))
raw=s.replace(raw,np,(odd,nn[1][1]))
cursor=0
def simplify(n):
 global cursor
 if s.leaf(n):
  i=cursor;cursor+=1
  return None if 2762<=i<2856 else n
 a,c=simplify(n[0]),simplify(n[1])
 return c if a is None else a if c is None else (a,c)
compact=simplify(raw)

loop=((q.CD(5),(q.CD(5),q.CD(5))),q.CD(5)),q.ubody
decoder=q.CD(5),(q.CD(5),loop)
no_prefix=[]
for k,tests in enumerate(q.assocs((q.CD(5),)*4)):
 n=tests,q.ubody
 counterexample=None
 for h in range(0,128,2):
  rr=[3,4,5,0,6,h,0,0,7]
  try:out,_=q.sim(n,rr,50000)
  except RuntimeError:
   counterexample={'h':h,'status':'50000-step finite simulation cap exceeded'};break
  want=rr.copy();want[5]=0;want[6],want[7]=q.unp(h//4)
  if out!=want:
   counterexample={'h':h,'actual':out,'expected':want};break
 no_prefix.append({'association':k,'first_even_counterexample':counterexample})
assert all(r['first_even_counterexample'] is not None for r in no_prefix)

newcmp=s.subtree(OLD,'111110')
records=[];trees=[];checks={}
for cname,cmp in [('new_open_E',newcmp),('old_closed_E',q.compare)]:
 core=cmp,q.move71
 ms=q.assocs((decoder,q.move65,q.move16,core,q.clear7))
 assert len(ms)==14 and all(s.boundary(n)==(0,0,False) for n in ms)
 checks[cname]=q.check_mp(ms[0])
 for rname,source in [('full_rho1',raw),('compact_rho1',compact)]:
  for k,n in enumerate(ms):
   tr=s.replace(source,'1111',n)
   rr=s.sites(tr);assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
   rec={'rho1':rname,'comparator':cname,'association':k,
        'metrics':s.metrics(tr),'mp_metrics':s.metrics(n)}
   records.append(rec);trees.append(tr)
minimum=min(r['metrics']['dag_nodes'] for r in records)
compiled=0
for k,(rec,tr) in enumerate(zip(records,trees)):
 if rec['metrics']['dag_nodes']!=minimum or compiled>=12:continue
 compiled+=1;d=OUT/f'best{k}';d.mkdir(exist_ok=True)
 (d/'sites.json').write_bytes(s.compact(s.sites(tr)))
 try:
  U,meta=compiler.compile_tree(T,OLD,tr,extend_direct=True);rec['compiler']=meta
  (d/'candidate.tm').write_bytes(b.table_bytes(U))
 except Exception as exc:
  rec['error']=repr(exc)
  (d/'candidate.tm').unlink(missing_ok=True)
 (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
summary={'status':'EXPLORATORY_SOURCE_AND_DECODER_ONLY',
 'logical_scope':'Old rho6, raw J disequality, Eq=N J, parity halt; inverse decoder exact on I/Q, arbitrary on odd tags',
 'source_layouts':len(records),'minimum_DAG':minimum,
 'minimum_compiler_count':min((r['compiler']['working_states'] for r in records if 'compiler'in r),default=None),
 'compiled_minimum_representatives':compiled,
 'finite_mp_checks_per_comparator':checks,
 'rejected_11_leaf_associations':no_prefix,'records':records}
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='records'}),flush=True)
