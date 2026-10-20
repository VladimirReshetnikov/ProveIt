#!/usr/bin/env python3
"""Contract two checked zero-only source components of published219.

The induction premise is rechecked independently.  The retained source CFG is
then checked after skipping each deleted zero entry.  No bounded machine run
is used to establish this source transformation.
"""
from pathlib import Path
import json,sys
from hardware_objective219 import ROOT,model,r
sys.path.insert(0,str(ROOT/'theory_notes'));from audit_abstract_certificate import check
p=ROOT/'baseline219/K219_Construction_2026-10-20/machine'
rows=json.loads((p/'sites219.json').read_text());tree=r.normalise(r.s.tree(rows));T=r.b.read_table((p/'k219.native.tm').read_bytes())
inv=json.loads((ROOT/'machine218/abstract219.json').read_text());audit=check(rows,inv['domains'],[3,0,0,0,3,0,0,0,0])
G=r.s.graph_arithmetic(rows)[0];assert G==r.s.graph_intervals(rows)
evaluate,meta=model(T,tree,json.loads((ROOT/'source218/frozen_engine_rows219.json').read_text())['rows'])
out=ROOT/'source218/seeded_deletions';out.mkdir(exist_ok=True)
specs={'equality_cleanup':('1110100101100110',4606,6,{4606,4607}),
       'tail_noop':('11111100',4718,1,{4718,4719,4720})}
assert audit['always_zero_decrements']==[4606,4718]
for name,keys in [('equality_cleanup',['equality_cleanup']),('tail_noop',['tail_noop']),('both',['equality_cleanup','tail_noop'])]:
 n=tree;removed=set();zero={}
 for key in keys:
  path,entry,reg,indices=specs[key];assert path.endswith('0')
  assert {i for i,x in enumerate(rows)if x[0].startswith(path)}==indices
  parent=path[:-1];sibling=r.s.subtree(n,parent)[1]
  n=r.normalise(r.s.replace(n,parent,sibling));removed.update(indices);zero[entry]=G[entry][1][0]
 fresh=r.s.sites(n);retained=[i for i in range(len(rows))if i not in removed]
 assert len(fresh)==len(retained)
 def skip(i):
  seen=set()
  while i in removed:
   assert i not in seen and i in zero,(i,removed,zero)
   seen.add(i);i=zero[i]
  return i
 translate={old:new for new,old in enumerate(retained)}
 expected=[[rec[0],[translate[skip(j)]for j in rec[1]]]for i in retained for rec in[G[i]]]
 # The two exact contractions do not need changed control operands.
 assert [x[1:]for x in fresh]==[rows[i][1:]for i in retained]
 assert r.s.graph_arithmetic(fresh)[0]==r.s.graph_intervals(fresh)==expected
 folder=out/name;folder.mkdir(exist_ok=True);(folder/'sites.json').write_bytes(r.s.compact(fresh))
 report=dict(status='SEEDED_ZERO_COMPONENT_CONTRACTION_PASS',removed_indices=sorted(removed),zero_entries=zero,
             invariant_audit=audit,primitive_effects_equal_on_retained_ordinals=True,
             all_retained_successors_equal_after_zero_contraction=True,hardware=evaluate(n),
             scope='Seeded source equivalence under the independently checked inductive invariant. No final TM allocation or blank bootstrap is asserted.')
 (folder/'certificate.json').write_text(json.dumps(report,indent=2)+'\n');print(name,json.dumps(report['hardware']),flush=True)
