#!/usr/bin/env python3
"""Recompute producer hash comparisons and capture-relative BFS rebuild graph; no Lean replay."""
from pathlib import Path
from hashlib import sha256
from collections import deque
import json,re
D=Path(__file__).resolve().parents[2];H=D/'research/direct-bfs-80-coherent-rebuild-plan';P=H/'observations/attempt01/result.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def j(p):return json.loads(Path(p).read_text())
assert sha(P)=='14c9a694d6574037e70044fcec7ef12aae0d399ce1341add86cdafd1d0388893' and sha(H/'plan.py')=='6675f1cdca5fd0eae0c331c60fd9e9d762e225f42f158c5ed085287c4969688a'
r=j(P)
for name,x in r['inputs'].items():assert sha(x['path'])==x['sha256'],name
I=r['inputs']; a=j(I['fixed_capture']['path']);b=j(I['rebuilt_capture']['path']);run=j(I['rebuilt_run']['path']);n=j(I['old_negative_state']['path']);t=j(I['old_ratio_receipt']['path']); A=a['closure']['project'];E=a['closure']['outside'];B=b['selected_project'];st={x['module']:x for x in run['stages']}
assert a['status']=='PASS_CAPTURE' and b['status']=='PASS' and run['status']=='PASS'
neg=next(x for x in n['records'] if x['module']=='DiophantineConsistency.ArithmeticNegativeNorms'); assert neg['exit']==0 and neg['verified'];assert t['status']=='PASS' and t['module']=='DiophantineConsistency.ModelRatioBounds'
old=[neg,t]; sources=[I['old_negative_source']['sha256'],I['old_ratio_source']['sha256']]
for x,record,source in zip(r['mismatch_producers'],old,sources):
 module=x['module'];assert module in A and module in B and module in st
 oldout=record['object_sha256'] if 'object_sha256' in record else record['output']['sha256'];assert oldout==x['old_object']==A[module]['record']['sha256']==sha(A[module]['path'])
 assert record['source_sha256']==source==x['shared_source']==st[module]['source_sha256']
 source_paths=[Path(c) for c in st[module]['command'] if c.endswith('.lean')];assert len(source_paths)==1 and sha(source_paths[0])==source
 assert x['new_object']==B[module]['.olean']['sha256']==st[module]['output']['.olean']['sha256']==sha(B[module]['.olean']['path'])
 assert st[module]['exit']==0 and st[module]['reason'] is None and st[module]['index']==x['rebuilt_stage_index']
 assert x['old_serialized_imports']==A[module]['imports']==x['rebuilt_serialized_imports']==b['headers'][module]
 deps=record['dependency_hashes'] if 'dependency_hashes' in record else {k:v['record']['sha256'] for k,v in record['direct'].items()}
 assert deps==x['old_producer_direct_hashes']
 cur={k:(A.get(k) or E.get(k))['record']['sha256'] for k in deps};assert cur==x['fixed_selected_direct_hashes']
 diff={k:{'producer':v,'fixed_selected':cur[k]} for k,v in deps.items() if cur[k]!=v};assert diff==x['producer_direct_drift']
 print(module,'differences',json.dumps(diff,sort_keys=True))
assert len(r['mismatch_producers'][0]['producer_direct_drift'])==1 and len(r['mismatch_producers'][1]['producer_direct_drift'])==3
seeds={x['module'] for x in r['mismatch_producers']};rev={name:set() for name in A}
for name,row in A.items():
 for dep in row['imports']:
  if dep in rev:rev[dep].add(name)
seen=set(seeds); todo=deque(seeds)
while todo:
 for dep in rev[todo.popleft()]:
  if dep not in seen:seen.add(dep);todo.append(dep)
assert len(seen)==84 and sorted(seen & set(B))==r['affected_already_rebuilt'] and len(r['affected_already_rebuilt'])==19
rebuild=seen-set(B);sup=set(A)-set(B)-rebuild;assert len(rebuild)==65 and len(sup)==101 and sorted(sup)==r['unaffected_missing_supplements']
assert all(name in st and st[name]['exit']==0 and st[name]['reason'] is None for name in seen&set(B))
remaining=set(rebuild);expected=[]
while remaining:
 ready=sorted(name for name in remaining if not(set(A[name]['imports']) & remaining));assert ready
 expected+=ready;remaining.difference_update(ready)
assert expected==[x['module'] for x in r['rebuild_order']]
no=0
for i,x in enumerate(r['rebuild_order'],1):
 name=x['module'];p=x['producer'];rp=Path(p['receipt']);sp=Path(p['source_snapshot']);q=j(rp)
 assert i==x['index'] and sha(rp)==p['receipt_sha256'] and sha(sp)==p['source_sha256']==q['pins']['source']
 assert q['pins']==q['after'] and q['exit']==0 and q['reason'] is None and q['object_sha256']==A[name]['record']['sha256']==x['old_selected_object']['sha256']
 assert x['captured_imports']==A[name]['imports'] and re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',sp.read_text(),re.M)==[v for v in A[name]['imports'] if v!='Init']
 assert x['dependencies_in_rebuild']==sorted(set(A[name]['imports'])&rebuild)
 assert len(q.get('direct_imports',[]))==p['recorded_direct_import_count'];no+=p['recorded_direct_import_count']==0
assert no==8 and r['report']=={'affected':84,'affected_already_rebuilt':19,'affected_to_rebuild':65,'unaffected_missing_supplements':101,'stages_with_no_recorded_direct_imports':8}
print('PASS 84 captured reverse-reachable names, 19 previously rebuilt, 65 topologically ordered source/receipt snapshots, 101 outside cone supplements; 8 lack direct-import records')
print('Only recorded producer object hash equality, not unique producer or complete historical/package/dynamic ancestry; no Lean replay or rebuild.')
