#!/usr/bin/env python3
"""Independently recount the frozen post-120 source and recorded-edge survey."""
from collections import defaultdict, deque
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

D = Path(__file__).resolve().parent
V = D.parent
ROOT = D.parents[3]
survey = V / 'ipra-current-repaired-post120-final-source-survey'
manifest_path = survey / 'manifest.json'
old_path = V / 'ipra-current-repaired-post159-final-source-survey/manifest.json'
plan_path = V / 'ipra-frozen-repair-plan-v2/manifest.json'
origin_path = V / 'ipra-current-repaired-survey/manifest.json'
H = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
m = json.loads(manifest_path.read_text())
old = json.loads(old_path.read_text())
plan = json.loads(plan_path.read_text())
origin = json.loads(origin_path.read_text())
assert m['status'] == 'CANDIDATE_SOURCE_SNAPSHOT' and len(m['sources']) == 1099
assert m['head_before'] == m['head_after'] and not m['workspace_drift_before'] and not m['workspace_drift_after']
for p, h in m['input_sha256'].items():
    assert H(p) == h, ('input changed', p)
seeds = {name for name, row in m['sources'].items() if row['sha256'] != old['sources'][name]['sha256']}
assert seeds == set(m['seeds']) and len(seeds) == 11
workspace_drift = []
for name, row in m['sources'].items():
    source = survey / 'sources' / (name.replace('.', '/') + '.lean')
    assert source.is_file() and not source.is_symlink() and H(source) == row['sha256'], name
    imports = re.findall(r'^import\s+([A-Z][\w.]*)', source.read_text(), re.M)
    assert imports == row['imports'], ('import mismatch', name)
    workspace = ROOT / row['path']
    if not workspace.is_file() or H(workspace) != row['sha256']:
        workspace_drift.append(name)

paths = [Path(p) for p in ('/tmp/ipra-post159-replay-6c04l2wf/state.json',
         '/tmp/ipra-post172-replay-81f0339y/state.json',
         '/tmp/ipra-eleven-drift-replay-sfz0zyj0/state.json',
         '/tmp/ipra-six-drift-replay-42b7hj5k/state.json',
         '/tmp/ipra-current-repaired-build-y6kamkla/state.json')]
paths.append(Path(origin['parent']) / 'state.json')
edges = set()
for owner, row in m['sources'].items():
    edges.update((dep, owner) for dep in row['imports'])
for path in paths:
    state = json.loads(path.read_text())
    assert state['status'] == 'PASS'
    for row in state['records']:
        edges.update((dep, row['name']) for dep in row['direct_imports'])
for row in plan['origin_nodes'].values():
    edges.update((dep, row['module']) for dep in row['project_environment'])
successors = defaultdict(set)
for dep, owner in edges:
    successors[dep].add(owner)
affected = set(seeds)
queue = deque(seeds)
while queue:
    for owner in successors[queue.popleft()]:
        if owner not in affected:
            affected.add(owner)
            queue.append(owner)
order = m['order']
assert len(order) == len(set(order)) == 351 and affected == set(order)
position = {name: i for i, name in enumerate(order)}
internal = {(dep, owner) for dep, owner in edges if dep in affected and owner in affected}
assert all(position[dep] < position[owner] for dep, owner in internal)
assert len(internal) == 12751 and order[-1] == m['target']
header = json.loads((survey / 'lean-deps-receipt.json').read_text())
assert set(header['rows']) == seeds
for p, h in header['input_sha256'].items():
    assert H(p) == h, ('header input changed', p)
for name, row in header['rows'].items():
    assert hashlib.sha256(row['stdout'].encode()).hexdigest() == row['stdout_sha256'], name
    assert row['count'] == len(set(m['sources'][name]['imports']) - {'Init'}), name
    env = dict(os.environ, LEAN_PATH='/tmp/ipra-post159-replay-6c04l2wf/lib:/tmp/pra14-full-transitive-2x6o__to/package-lib')
    env.pop('LEAN_SRC_PATH', None)
    path = survey / 'sources' / (name.replace('.', '/') + '.lean')
    proc = subprocess.run(['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean', '--deps', str(path)],
                          env=env, capture_output=True, text=True)
    assert proc.returncode == 0 and not proc.stderr and proc.stdout == row['stdout'], ('header replay', name)
print('PASS frozen sources', len(m['sources']), 'seeds', len(seeds),
      'affected', len(affected), 'recorded internal edges', len(internal))
print('PASS independently repeated Lean dependency parsing for', len(header['rows']), 'changed headers')
print('workspace changes since capture:', ', '.join(sorted(workspace_drift)) or 'none')
print('scope: source and recorded-edge audit only; physical origins and replay remain open')
