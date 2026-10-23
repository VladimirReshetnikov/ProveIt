"""Independent live-node counts, acyclicity, and variable checks."""
import json
from pathlib import Path
from collections import Counter
root=Path(__file__).resolve().parents[1]
paths=['sun/generated/sun_b4.json','signed_audit/generated/signed13_b4.json','signed_audit/generated/signed14_b4.json','nine/generated/nine_b4_natural.json','nine/generated/nine_b4_positive.json']
rows=[]
for p in paths:
 x=json.loads((root/p).read_text());nodes=x['nodes'];seen=set();todo=[x['output']]
 while todo:
  i=todo.pop()
  if i in seen:continue
  assert 0<=i<len(nodes);seen.add(i);n=nodes[i]
  if n['kind'] in ['add','sub','mul']:
   assert 0<=n['left']<i and 0<=n['right']<i
   todo += [n['left'],n['right']]
  else:assert n['kind'] in ['literal','fixed','variable']
 counts=Counter(nodes[i]['kind'] for i in seen)
 assert set(n['name'] for i,n in enumerate(nodes) if i in seen and n['kind']=='variable')==set(x['variables'])
 assert {k:counts[k] for k in ['add','sub','mul']}==x['operation_counts']
 assert x['exact_degree']>0
 rows.append({'file':p,'variables':counts['variable'],'fixed_leaves':counts['fixed'],'live_nodes':len(seen),'operations':sum(counts[k] for k in ['add','sub','mul']),'counts':dict(counts),'degree':x['exact_degree']})
Path(__file__).with_name('dag_structure_checks.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
