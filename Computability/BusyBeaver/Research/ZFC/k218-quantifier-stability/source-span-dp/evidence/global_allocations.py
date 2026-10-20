#!/usr/bin/env python3
from pathlib import Path
import sys,json
sys.dont_write_bytecode=True
import source_language as s,build221 as b,measure_pinned as m,global_allocator_v2 as g
P=Path(__file__).resolve().parent;plan=json.loads((P/'input.json').read_text());seed=Path(plan['seed'])
tree=s.tree(json.loads((seed/'sites218.json').read_text()));table=b.read_table((seed/'k218.native.tm').read_bytes())
assert m.sha((seed/'sites218.json').read_bytes())==plan['seed_source_sha256'] and m.sha((seed/'k218.native.tm').read_bytes())==plan['seed_table_sha256']
control,cm=g.compile_tree(s,b,table,tree,tree);assert control==table and cm['working_states']==218
out=P/'global-allocations';assert not out.exists();out.mkdir();rr=[]
for i in range(4):
 p=P/'verified'/f'candidate{i:03}';r=json.loads((p/'receipt.json').read_text());raw=(p/'sites.json').read_bytes();assert m.sha(raw)==r['source_sha256']
 t=s.tree(json.loads(raw));assert s.metrics(t)['dag_nodes']==208;rows=s.sites(t);assert s.graph_arithmetic(rows)[0]==s.graph_intervals(rows)
 d=out/f'candidate{i:03}';d.mkdir()
 try:
  tt,rec=g.compile_tree(s,b,table,tree,t,require_pure_rows=True,hypothetical_entries=False)
  (d/'raw.tm').write_bytes(b.table_bytes(tt));result={'candidate':i,'status':'RAW_PREFIX_BINDING_PASS','compiler':rec}
 except (ValueError,AssertionError,KeyError)as e:result={'candidate':i,'status':'ALLOCATION_REJECTED','error':repr(e)}
 (d/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');rr.append(result);print(i,result.get('error',result.get('compiler',{}).get('working_states')),flush=True)
(out/'result.json').write_text(json.dumps({'status':'BOUNDED_EXISTING_GLOBAL_ALLOCATOR_DIAGNOSTIC','identity':cm,'results':rr,'allocator_sha256':m.sha((P/'global_allocator_v2.py').read_bytes()),'scope':'Strict existing global-pool policy; no hypothetical leaf actions. Prefix binding only, no runtime or startup acceptance.'},indent=2)+'\n')
