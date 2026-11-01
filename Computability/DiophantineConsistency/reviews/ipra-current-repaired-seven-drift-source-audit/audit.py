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
N = V / 'ipra-current-repaired-seven-drift-source-survey'
B = V / 'ipra-current-repaired-six-drift-source-survey'
P = V / 'ipra-frozen-repair-plan-v2' / 'manifest.json'
T = Path('/tmp/ipra-current-repaired-build-y6kamkla/state.json')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs = [Path(__file__).resolve(), N/'manifest.json', N/'lean-deps-receipt.json', B/'manifest.json', P, T]
before = {str(p): H(p) for p in inputs}
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
m, old, plan, parent = (json.loads(p.read_text()) for p in (N/'manifest.json', B/'manifest.json', P, T))
assert m['status'] == 'CANDIDATE_SOURCE_SNAPSHOT' and old['status'] == 'CANDIDATE_SOURCE_SNAPSHOT'
assert parent['status'] == 'PASS' and len(parent['records']) == 258
assert not m['workspace_drift_before'] and not m['workspace_drift_after']
assert m['head_before'] == m['head_after'] and len(m['sources']) == 1099
assert set(m['sources']) == set(old['sources']) and m['external'] == old['external']
seed = 'ZFCinPA.SeparationKernel'
assert m['seed'] == seed
changed = []
rev = defaultdict(set)
for name, row in m['sources'].items():
    source = N/'sources'/(name.replace('.', '/')+'.lean')
    assert source.is_file() and not source.is_symlink() and H(source) == row['sha256'], name
    assert H(R/row['path']) == row['sha256'], name
    assert row['path'] == old['sources'][name]['path']
    imports = re.findall(r'^import\s+([A-Z][\w.]*)', source.read_text(), re.M)
    assert imports == row['imports'], name
    if row != old['sources'][name]: changed.append(name)
    for dependency in imports: rev[dependency].add(name)
assert changed == [seed]
assert set(m['sources'][seed]['imports']) - set(old['sources'][seed]['imports']) == {'ZFCinPA.ModelCodedSchemaAxioms'}
assert set(old['sources'][seed]['imports']) <= set(m['sources'][seed]['imports'])
for row in plan['origin_nodes'].values():
    for dependency in row['project_environment']: rev[dependency].add(row['module'])
for row in parent['records']:
    for dependency in row['direct_imports']: rev[dependency].add(row['name'])
queue, affected = deque([seed]), {seed}
while queue:
    for owner in rev[queue.popleft()]:
        if owner not in affected:
            affected.add(owner)
            queue.append(owner)
order = m['order']
assert len(order) == len(set(order)) == len(affected) == 80 and set(order) == affected
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
assert receipt['status'] == 'PASS_HEADER_DEPS' and receipt['module'] == seed
assert hashlib.sha256(receipt['stdout'].encode()).hexdigest() == receipt['stdout_sha256']
assert H(N/'manifest.json') == '1d1d80a67fcec78693d815a803d49f57cf5533b410c1e58edc33e848f4ea77b5'
assert H(N/'lean-deps-receipt.json') == 'a4b90bf7923a47902e0ab6a1db6041347cfb3403a20d9473e8dcbf206f2619be'
assert {str(p): H(p) for p in inputs} == before
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip() == head
out = {'status':'PASS_SOURCE_SNAPSHOT', 'source_count':len(m['sources']), 'changed':changed,
       'conservative_affected':len(affected), 'input_sha256':before, 'head':head,
       'scope':'Frozen source bytes, direct header extraction, source closure, recorded-edge reverse closure and captured receipt; not a current object-origin or replay audit.'}
path = D/'receipt.json'
assert not path.exists()
path.write_text(json.dumps(out, sort_keys=True, indent=2)+'\n')
print('PASS_SOURCE_SNAPSHOT', len(m['sources']), 'sources;', len(affected), 'affected; seed', seed)
