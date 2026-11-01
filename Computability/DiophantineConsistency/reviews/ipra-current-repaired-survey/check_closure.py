#!/usr/bin/env python3
"""Independently reconstruct the survey's project-origin rebuild closure."""
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path

D = Path(__file__).resolve().parent
ROOT = D.parents[3]
REVIEW = ROOT / 'Computability/DiophantineConsistency/reviews'
MANIFEST = D / 'manifest.json'
PLAN = REVIEW / 'ipra-frozen-repair-plan-v2/manifest.json'
PARENT = Path('/tmp/ipra-frozen-ancestry-repair-6ftdeyrq')
EXT = {'Foundation', 'Mathlib', 'Lean', 'Init', 'Std', 'Batteries', 'Qq',
       'Aesop', 'Plausible', 'ProofWidgets', 'ImportGraph', 'LeanSearchClient', 'Lake'}
@lru_cache(maxsize=None)
def h(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(p):
    return json.loads(Path(p).read_text())
m, p, s = read(MANIFEST), read(PLAN), read(PARENT / 'state.json')
assert h(str(PLAN)) == m['repair_plan_sha256']
assert h(str(PARENT / 'state.json')) == m['parent_state_sha256']
assert s['status'] == 'PASS' and s['manifest_sha256'] == h(str(PLAN))
rows = {r['name']: r for r in s['records']}
assert list(rows) == p['order']
assert all(v['exit'] == 0 and not v['warnings'] for v in rows.values())
snapshots = m['sources']
origins = {(v['module'], v['sha256'], v['physical_path']): v
           for v in p['origin_nodes'].values()}
selected = m['selected_project_objects']
edges = {}
seeds = set()
for name, old_hash in p['source_sha256'].items():
    ns = name.split('.')[0]
    if ns not in m['roots']:
        seeds.add(name)
        continue
    path = ROOT / m['roots'][ns] / (name.replace('.', '/') + '.lean')
    if not path.is_file() or h(str(path)) != old_hash:
        seeds.add(name)
for name, info in snapshots.items():
    frozen = D / 'sources' / (name.replace('.', '/') + '.lean')
    assert h(str(frozen)) == info['sha256']
    assert h(str(ROOT / info['path'])) == info['sha256'], ('workspace drift', name)
    dependencies = {x for x in info['imports'] if x.split('.')[0] not in EXT}
    assert dependencies <= snapshots.keys(), ('unresolved source import', name)
    if name not in p['source_sha256']:
        seeds.add(name)
    sel = selected.get(name)
    if sel is None:
        seeds.add(name)
        edges[name] = dependencies
        continue
    obj = PARENT / 'lib' / (name.replace('.', '/') + '.olean')
    assert str(obj.resolve()) == sel['path'] and h(str(obj)) == sel['sha256']
    if name in rows:
        row = rows[name]
        assert sel['sha256'] == row['object_sha256']
        env = {k: v['sha256'] for k, v in row['direct_imports'].items() if k.split('.')[0] not in EXT}
        for dep, val in row['direct_imports'].items():
            if dep.split('.')[0] in EXT:
                assert h(val['resolved_path']) == val['sha256']
    else:
        node = origins.get((name, sel['sha256'], sel['path']))
        if node is None:
            seeds.add(name)
            edges[name] = dependencies
            continue
        assert h(node['source_path']) == node['source_sha256']
        env = node['project_environment']
    for dep, expected in env.items():
        obj = PARENT / 'lib' / (dep.replace('.', '/') + '.olean')
        if not obj.is_file() or h(str(obj)) != expected:
            seeds.add(name)
    edges[name] = dependencies | set(env)
closure = set(seeds)
while True:
    enlarged = closure | {n for n, deps in edges.items() if deps & closure}
    if enlarged == closure:
        break
    closure = enlarged
affected = closure & snapshots.keys()
assert affected == set(m['order'])
assert len(m['order']) == len(affected)
indices = {n: i for i, n in enumerate(m['order'])}
for name in affected:
    for dep in snapshots[name]['imports']:
        if dep in affected:
            assert indices[dep] < indices[name], (name, dep)
assert indices[m['target']] == len(indices) - 1
for module, info in m['external'].items():
    for path, val in info['companions'].items():
        if val is None:
            assert not os.path.lexists(path), ('unexpected external file or symlink', path)
        else:
            assert Path(path).resolve() == Path(val['realpath']) and h(path) == val['sha256']
receipt = {'manifest_sha256': h(str(MANIFEST)), 'checker_sha256': h(__file__),
           'sources': len(snapshots), 'rebuild': len(affected), 'initial_seeds': sorted(seeds),
           'selected_project_objects': len(selected), 'direct_external_modules': len(m['external']),
           'status': 'PASS', 'scope': 'Independent fixed-point project closure; inherits the '
              'earlier original-provider audits and external transitive/dynamic boundaries.'}
(D / 'closure-receipt.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print('PASS', len(snapshots), 'sources', len(affected), 'rebuild')
