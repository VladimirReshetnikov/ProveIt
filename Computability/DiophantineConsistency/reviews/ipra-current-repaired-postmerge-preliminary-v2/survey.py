#!/usr/bin/env python3
"""Source-only prospective reverse-closure sizing; not a replay plan."""
import collections
import graphlib
import hashlib
import json
from pathlib import Path
import re
import subprocess

D = Path(__file__).resolve().parent
V = D.parent
R = D.parents[3]
SUR = V / 'ipra-current-repaired-survey' / 'manifest.json'
PLAN = V / 'ipra-frozen-repair-plan-v2' / 'manifest.json'
STATE = Path('/tmp/ipra-frozen-ancestry-repair-6ftdeyrq/state.json')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs = [Path(__file__).resolve(), SUR, PLAN, STATE]
before = {str(p): H(p) for p in inputs}
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
s, p, st = (json.loads(x.read_text()) for x in (SUR, PLAN, STATE))
assert st['status'] == 'PASS' and H(STATE) == s['parent_state_sha256']
assert H(PLAN) == s['repair_plan_sha256']
assert len(s['sources']) == 1099 and len(s['order']) == 258
records = {row['name']: row for row in st['records']}
nodes = {(x['module'], x['sha256'], x['physical_path']): x for x in p['origin_nodes'].values()}
rev = collections.defaultdict(set)
drift = {}
unmatched = []
rebuilt = set(s['order'])
for name, row in s['sources'].items():
    path = R / row['path']
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != row['sha256']:
        actual = re.findall(r'^import\s+([A-Z][\w.]*)', raw.decode('utf-8'), re.M)
        assert actual == row['imports'], ('changed explicit imports need a fresh graph', name)
        drift[name] = {'captured': row['sha256'], 'workspace': digest, 'path': row['path']}
    for dependency in row['imports']:
        rev[dependency].add(name)
    if name in rebuilt:
        continue
    if name in records:
        env = records[name]['direct_imports']
    else:
        obj = s['selected_project_objects'].get(name)
        node = nodes.get((name, obj['sha256'], obj['path'])) if obj else None
        if node is None:
            unmatched.append(name)
            continue
        env = node['project_environment']
    for dependency in env:
        rev[dependency].add(name)
expected = {'DiophantineConsistency.PRAWitnessPR', 'DiophantineConsistency.PRAWitnessZFCAxioms',
            'ZFCinPA.LStepAnd', 'ZFCinPA.LStepBasic', 'ZFCinPA.LStepEx'}
assert set(drift) == expected and not unmatched
impacted = set(drift)
queue = list(impacted)
while queue:
    for owner in rev[queue.pop()]:
        if owner not in impacted:
            impacted.add(owner)
            queue.append(owner)
assert impacted <= set(s['sources'])
order = list(graphlib.TopologicalSorter({
    name: [dep for dep in s['sources'][name]['imports'] if dep in impacted]
    for name in sorted(impacted)
}).static_order())
assert all(H(R / row['path']) == drift.get(name, {}).get('workspace', row['sha256'])
           for name, row in s['sources'].items())
assert {str(path): H(path) for path in inputs} == before
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip() == head
out = {'status': 'PRELIMINARY_SOURCE_REVERSE_CLOSURE', 'head': head,
       'input_sha256': before, 'drift': drift, 'impacted': sorted(impacted),
       'source_topological_order': order, 'unmatched_retained_origins': unmatched,
       'boundary': 'Source and recorded-environment graph sizing only. Physical object origins, '
                   'current Lean dependency parsing, new source snapshots, completed 258 parent '
                   'and comparator, external companions and a successor replay remain unauthenticated here.'}
path = D / 'manifest.json'
assert not path.exists(), 'refusing to overwrite evidence'
path.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
print('PRELIMINARY_SOURCE_REVERSE_CLOSURE', len(drift), len(impacted), H(path))
