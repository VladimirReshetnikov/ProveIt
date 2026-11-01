#!/usr/bin/env python3
"""Independent source-only audit; this does not validate Lean object ancestry."""
import hashlib
import json
import re
import subprocess
from collections import defaultdict, deque
from pathlib import Path

D = Path(__file__).resolve().parent
V = D.parent
R = D.parents[3]
N = V / 'ipra-current-repaired-post159-preliminary-source-survey'
B = V / 'ipra-current-repaired-post172-source-survey'
P = V / 'ipra-frozen-repair-plan-v2' / 'manifest.json'
T = Path('/tmp/ipra-current-repaired-build-y6kamkla/state.json')
U = Path('/tmp/ipra-six-drift-replay-42b7hj5k/state.json')
W = Path('/tmp/ipra-eleven-drift-replay-sfz0zyj0/state.json')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs = [Path(__file__).resolve(), N/'manifest.json', N/'lean-deps-receipt.json', B/'manifest.json', P, T, U, W]
before = {str(p): H(p) for p in inputs}
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
m, old, plan, parent, parent107 = (json.loads(p.read_text()) for p in (N/'manifest.json', B/'manifest.json', P, T, U))
assert m['status'] == 'CANDIDATE_SOURCE_SNAPSHOT' and old['status'] == 'CANDIDATE_SOURCE_SNAPSHOT'
parent172 = json.loads(W.read_text())
assert parent172['status'] == 'PASS' and len(parent172['records']) == 172
assert parent['status'] == parent107['status'] == 'PASS' and len(parent['records']) == 258 and len(parent107['records']) == 107
assert not m['workspace_drift_before'] and not m['workspace_drift_after']
assert len(m['sources']) == 1099
assert set(m['sources']) == set(old['sources']) and m['external'] == old['external']
seeds = {'ZFCinPA.LGlueCodes','ZFCinPA.SetCongruence'}
workspace_drift = []
changed = []
rev = defaultdict(set)
for name, row in m['sources'].items():
    source = N/'sources'/(name.replace('.', '/')+'.lean')
    assert source.is_file() and not source.is_symlink() and H(source) == row['sha256'], name
    if H(R/row['path']) != row['sha256']: workspace_drift.append(name)
    assert row['path'] == old['sources'][name]['path']
    imports = re.findall(r'^import\s+([A-Z][\w.]*)', source.read_text(), re.M)
    assert imports == row['imports'], name
    if row != old['sources'][name]: changed.append(name)
    for dependency in imports: rev[dependency].add(name)
assert set(changed) == seeds and len(changed) == 2
assert all(m['sources'][n]['imports'] == old['sources'][n]['imports'] for n in seeds)
for row in plan['origin_nodes'].values():
    for dependency in row['project_environment']: rev[dependency].add(row['module'])
for state in (parent,parent107,parent172):
    for row in state['records']:
        for dependency in row['direct_imports']: rev[dependency].add(row['name'])
queue, affected = deque(seeds), set(seeds)
while queue:
    for owner in rev[queue.popleft()]:
        if owner not in affected:
            affected.add(owner)
            queue.append(owner)
order = m['order']
assert len(order) == len(set(order)) == len(affected) == 105 and set(order) == affected
pos = {name:i for i,name in enumerate(order)}
assert all(pos[dep] < pos[name] for name in order for dep in m['sources'][name]['imports'] if dep in pos)
assert order[-1] == m['target']
reachable, queue = set(), [m['target']]
while queue:
    name = queue.pop()
    if name not in reachable:
        reachable.add(name)
        queue.extend(x for x in m['sources'][name]['imports'] if x in m['sources'])
assert reachable == set(m['sources'])
receipt = json.loads((N/'lean-deps-receipt.json').read_text())
assert receipt['status'] == 'PASS_HEADER_DEPS'
assert set(receipt['rows']) == seeds
for name, row in receipt['rows'].items():
    assert hashlib.sha256(row['stdout'].encode()).hexdigest() == row['stdout_sha256']
    paths = row['stdout'].splitlines()
    expected = m['sources'][name]['imports']
    assert row['count'] == len(expected)
    assert all(sum(p.endswith('/' + dep.replace('.', '/') + '.olean') for p in paths) == 1 for dep in expected), name
assert H(N/'manifest.json') == '73180bacb054a790f3d22be827842a61dad905591347ba2210e6097467cbbce3'
assert H(N/'lean-deps-receipt.json') == '8ecc31a01669cdd568746a0d3c3146388799443093e5f7a502e0013c4372c3d9'
assert {str(p): H(p) for p in inputs} == before
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip() == head
out = {'status':'PASS_SOURCE_SNAPSHOT', 'source_count':len(m['sources']), 'changed':changed,
       'conservative_affected':len(affected), 'workspace_drift_at_audit':workspace_drift, 'input_sha256':before, 'head':head,
       'scope':'Frozen source bytes, direct header extraction, source closure, recorded-edge reverse closure and captured receipt; not a current object-origin or replay audit.'}
path = D/'receipt.json'
assert not path.exists()
path.write_text(json.dumps(out, sort_keys=True, indent=2)+'\n')
print('PASS_SOURCE_SNAPSHOT', len(m['sources']), 'sources;', len(affected), 'affected; current workspace drift', workspace_drift)
