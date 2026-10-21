#!/usr/bin/env python3
"""Guarded split-bundle cleanup also clears saved-c scratch7 on failure."""
from pathlib import Path
ns={'__name__':'split_support'}
src=Path(__file__).with_name('split_bundle219.py').read_text()
exec(src[:src.index('\nresults=[];best=999')],ns)
globals().update(ns)
OUT=q.W/'split_bundle_corrected219';OUT.mkdir(exist_ok=True)
C7=(CD(7),CC(1));results=[]
recipes={}
for name,parts in [('clear_pop6',(C7,C1,pop,C6)),('pop6_clear',(C7,pop,C6,C1)),('pop1_clear',(C7,pop,move61,C1)),('pop5_clear',(C7,pop5,C5,C1))]:
 for k,body in enumerate(q.assocs(parts)):recipes[f'{name}_a{k}']=(CD(1),body)
for name,action in {'pop_clear_E':((pop,C1),E),'clear_pop_E':((C1,pop),E),'pop_clearE':(pop,(C1,E)),'clear_popE':(C1,(pop,E))}.items():
 recipes[name]=(CD(1),(C7,action))
for name,action in recipes.items():
 gg=replacement(gate,action)
 try:count=checks(gg)
 except (AssertionError,RuntimeError)as exc:print('REJECT',name,str(exc)[:300],flush=True);continue
 tr=s.replace(without,GATE,gg);m=s.metrics(tr)
 rec={'name':name,'metrics':m,'gate_contract_cases':count,'status':'SOURCE_MACRO_CONTRACT_CHECKED; ENUMERATOR_COMPLETENESS_AND_RUNTIME_SEPARATE'}
 dd=OUT/name;dd.mkdir(exist_ok=True);rr=s.sites(tr);assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
 (dd/'sites.json').write_bytes(s.compact(rr))
 try:
  U,meta=compiler.compile_tree(T,OLD,tr,extend_direct=True);rec['compiler']=meta;(dd/'candidate.tm').write_bytes(b.table_bytes(U))
 except Exception as exc:rec['error']=repr(exc)
 (dd/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');results.append(rec);print(json.dumps(rec),flush=True)
(OUT/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
