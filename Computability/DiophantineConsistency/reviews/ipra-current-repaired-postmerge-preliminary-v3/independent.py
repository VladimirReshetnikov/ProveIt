#!/usr/bin/env python3
"""Independently reconstruct the preliminary source/environment fixed point."""
import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parent
V = D.parent
R = D.parents[3]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
survey = json.loads((V/'ipra-current-repaired-survey/manifest.json').read_text())
plan = json.loads((V/'ipra-frozen-repair-plan-v2/manifest.json').read_text())
statepath = Path('/tmp/ipra-frozen-ancestry-repair-6ftdeyrq/state.json')
state = json.loads(statepath.read_text())
target = json.loads((D/'manifest.json').read_text())
assert state['status'] == 'PASS' and sha(statepath) == survey['parent_state_sha256']
assert sha(V/'ipra-frozen-repair-plan-v2/manifest.json') == survey['repair_plan_sha256']
nodes = {(v['module'],v['sha256'],v['physical_path']):v for v in plan['origin_nodes'].values()}
rows = {v['name']:v for v in state['records']}
rebuilt = set(survey['order'])
drift, unmatched, edges = set(), [], {}
for name, info in survey['sources'].items():
    if sha(R/info['path']) != info['sha256']:
        drift.add(name)
    dependencies = set(info['imports'])
    if name not in rebuilt:
        if name in rows:
            dependencies.update(rows[name]['direct_imports'])
        else:
            obj = survey['selected_project_objects'].get(name)
            node = nodes.get((name,obj['sha256'],obj['path'])) if obj else None
            if node is None:
                unmatched.append(name)
            else:
                dependencies.update(node['project_environment'])
    edges[name] = dependencies
closure = set(drift)
while True:
    old = len(closure)
    closure.update(n for n,deps in edges.items() if deps & closure)
    if old == len(closure):
        break
assert drift == set(target['drift']) and closure == set(target['impacted'])
assert unmatched == target['unmatched_retained_origins']
order = target['source_topological_order']
indices = {n:i for i,n in enumerate(order)}
assert len(indices) == len(closure)
assert all(indices[d] < indices[n] for n in order for d in survey['sources'][n]['imports'] if d in indices)
receipt = {'status':'MATCHED_PRELIMINARY', 'drifts':len(drift), 'affected':len(closure),
           'manifest_sha256':sha(D/'manifest.json'), 'auditor_sha256':sha(__file__),
           'scope':'Source and recorded-environment sizing only; no completed parent or object-origin audit.'}
(D/'independent.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print('MATCHED_PRELIMINARY', len(drift), 'drifts,', len(closure), 'affected')
