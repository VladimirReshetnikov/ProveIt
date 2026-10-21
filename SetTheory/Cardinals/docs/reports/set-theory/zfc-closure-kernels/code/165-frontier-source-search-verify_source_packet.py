#!/usr/bin/env python3
"""Verify the frozen source constructions and exact finite-source metrics.
This does not verify an all-natural binary TM runtime or mathematical calibration.
"""
from pathlib import Path
import json,hashlib
import source_language as s
import source_splice as sp
P=Path(__file__).resolve().parent
def read(name):return s.tree(json.loads((P/name).read_text()))
def word(t):return[x[1:]for x in s.sites(t)]
base=read('sites215.json')
assert hashlib.sha256((P/'sites215.json').read_bytes()).hexdigest()=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
x=json.loads((P/'dag215.json').read_text());ns=[]
for n in x['nodes']:ns.append(tuple(n)if isinstance(n[0],str)else tuple(ns[i]for i in n))
assert ns[x['root']]==base
sources={
 'sites215.json':(202,4751,47,6),
 'G_I.json':(203,4750,47,6),
 'G_Q.json':(202,4752,47,6),
 'G_E.json':(204,4753,47,6),
 'G_sumAB1a.json':(204,4705,47,6),
 'Q_E_swap_ci_28_28.json':(203,4767,47,6),
 'tags_3102_0_202.json':(202,4824,46,10),
 'tags3102_binder0_0_202.json':(202,4823,46,10),
 'G_dup_1_0_5_210.json':(210,4695,47,6),
}
results=[]
for name,expected in sources.items():
 t=read(name);m=s.metrics(t)
 assert tuple(m.values())==expected,(name,m,expected)
 rows=s.sites(t);assert s.graph_intervals(rows)==s.graph_arithmetic(rows)[0]
 results.append({'file':name,**m,'independent_cfg_resolvers_agree':True})
for name,macro in [('G_I.json',ns[76]),('G_Q.json',ns[77]),('G_E.json',(ns[77],ns[37]))]:
 assert read(name)==sp.apply_closed_splices(base,{(695,723):macro})
assert word(read('G_sumAB1a.json'))==word(base)[:643]+word(ns[60])+word(ns[66])+[['CI',1]]+word(base)[723:]
calls=json.loads((P/'constructor_calls.json').read_text())
assert len(calls)==81
bw=word(base);pat=word(ns[76]);census={}
for c in calls:
 lo,bh,hi,tag=(c[k]for k in('lo','basehi','hi','tag'))
 assert bh-lo==27 and hi-bh==tag
 assert bw[lo:bh]==pat and bw[bh:hi]==[['CI',1]]*tag
 census[tag]=census.get(tag,0)+1
assert census=={0:41,1:12,2:22,3:6},census
def expected_tags(mp):
 out=[];at=0
 for c in calls:
  out.extend(bw[at:c['basehi']]);out.extend([['CI',1]]*mp[c['tag']]);at=c['hi']
 out.extend(bw[at:]);return out
assert word(read('Q_E_swap_ci_28_28.json'))==expected_tags({0:0,1:1,2:3,3:2})
assert word(read('tags_3102_0_202.json'))==expected_tags({0:3,1:1,2:0,3:2})
rt=read('tags_3102_0_202.json');rr=read('closed_tags_3102_0_202_best1_202_z8.json')
assert word(rt)==word(rr)
assert s.graph_intervals(s.sites(rt))==s.graph_intervals(s.sites(rr))
assert s.metrics(rr)['dag_nodes']==202 and s.metrics(rr)['maximum_zero_run']==8
for i in range(4):
 r=read(f'rowexact_{i}_202.json');assert s.metrics(r)==s.metrics(base)
out={'status':'SOURCE_CONSTRUCTION_CHECKS_PASS','scope':'Finite source trees, constructor words, metrics and guarded ordinal CFGs only. No binary candidate acceptance.','constructor_census':census,'sources':results,'closed_reassociation_cfg_preserved':True}
(P/'source_packet_verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

