#!/usr/bin/env python3
"""Independently reconstruct recorded project closure; no Lean invocation."""
from collections import deque
import hashlib
import json
import os
from pathlib import Path
import sys

if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):
    raise SystemExit('Run with python3 -I -S -B')
D = Path(__file__).resolve().parents[2]
P = Path('/tmp/p72-current-base-extension-attempt02-20261105')
B = Path('/tmp/current14-standard-fresh-build-20261104')
S = Path('/tmp/current14-standard-fresh-source-20261104')
A = D/'research/ordinary14-root74-recorded-ancestry-audit'

def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def read(path):
    return json.loads(path.read_text())

assert sha(A/'inspect.py') == '633464d9038aa4d1914067eacbd9c1b1a8b649cd47eb02f13234a1329f07298a'
assert sha(A/'observation.json') == '1c1a1afcb7fafe99d1544b714946adb3a2847032edf00923305ec4da47593c0a'
claim = read(A/'observation.json')
pins = {
 D/'research/ordinary14-root74-provider-survey/observation.json': '14732a54d8f2d3592d31f78d731497a1d804780ca8ec643e3851314868e7b4ab',
 P/'progress.json': 'f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a',
 P/'source-snapshot.json': '4536c44c399dc42037b692a39a36cc74c807693e1e5a76e2f5db299691fff7d8',
 P/'base-links.json': '16aa5524fd4e6fc65acd557a1e644d077e8dc70835c408411f5d5ae9597bfe24',
 B/'state.json': 'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014',
 S/'manifest.json': '1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749',
}
for path, digest in pins.items(): assert sha(path) == digest, str(path)
base = read(B/'state.json')
link = read(P/'base-links.json')
snap = read(P/'source-snapshot.json')
progress = read(P/'progress.json')
assert progress['status'] == base['status'] == 'PASS'
assert progress['source_snapshot_sha256'] == pins[P/'source-snapshot.json']
assert progress['base_links_sha256'] == pins[P/'base-links.json']
assert base['manifest_sha256'] == pins[S/'manifest.json']
files = sorted((P/'rows').glob('[0-9][0-9][0-9][0-9].json'))
assert len(files) == progress['total'] == progress['completed'] == len(snap) == 681
assert sha(files[-1]) == progress['last_row_sha256']
project = {}
for idx, path in enumerate(files):
    row = read(path)
    assert path.name == f'{idx:04}.json' and row['index'] == idx and row['status'] == 'PASS'
    assert row['module'] not in project
    project[row['module']] = ('p72', idx, row)
assert len(base['records']) == 1000
for idx, row in enumerate(base['records']):
    assert row['exit'] == 0 and row['module'] not in project
    project[row['module']] = ('base', idx, row)
seeds = read(D/'research/ordinary14-root74-provider-survey/observation.json')['slim_cut_frontier']
assert len(set(seeds)) == len(seeds) == 31

# Breadth-first reconstruction, deliberately using the records rather than
# the audited script or its output as the source of the edge set.
queue, visited, edges, external = deque(seeds), set(), [], {}
while queue:
    name = queue.popleft()
    if name in visited: continue
    assert name in project, name
    visited.add(name)
    group, i, row = project[name]
    inputs = row['dependencies'] if group == 'p72' else row['direct_inputs']
    for child, edge in inputs.items():
        if group == 'base':
            assert edge['kind'] in ('project','package')
            is_project = edge['kind'] == 'project'
        else:
            is_project = child in project
        if is_project:
            assert child in project
            target_group, j, _ = project[child]
            assert group != 'base' or target_group == 'base'
            if group == target_group: assert j < i
            queue.append(child)
        else:
            assert child == 'Init' or child.startswith(('Foundation.','Mathlib.','Lean.'))
            external.setdefault(child, set()).add((edge['path'],str(Path(edge['path']).resolve(strict=True)),edge['sha256']))
        edges.append((name,child,edge,is_project))

cache = {}
def file_observation(path):
    path = Path(path)
    if str(path) not in cache:
        real = path.resolve(strict=True)
        cache[str(path)] = {'realpath':str(real),'sha256':sha(real)}
    return cache[str(path)]

def module_path(root, name, suffix):
    return root.joinpath(*name.split('.')).with_suffix(suffix)

slots = {}
for name in sorted(visited):
    group, _, row = project[name]
    root, source_root = (P, P) if group == 'p72' else (B, S)
    source = module_path(source_root/'src', name, '.lean')
    obj = module_path(root/'lib', name, '.olean')
    assert file_observation(source)['sha256'] == row['source_sha256'], name
    assert file_observation(obj)['sha256'] == row['object_sha256'], name
    if group == 'p72':
        assert snap[name] == row['source_sha256']
        expected_slots = row['direct_guard']
    else:
        linked = module_path(P/'lib',name,'.olean')
        assert linked.is_symlink() and link[str(linked)] == str(obj)
        assert linked.resolve(strict=True) == obj.resolve(strict=True)
        expected_slots = base['outputs'][name]
    for path, expected in expected_slots.items():
        actual = file_observation(path) if os.path.lexists(path) else None
        assert actual == expected, path
        if path in slots: assert slots[path] == actual
        slots[path] = actual
for parent, child, edge, is_project in edges:
    actual = file_observation(edge['path'])
    assert actual['sha256'] == edge['sha256'], (parent,child)
    if project[parent][0] == 'p72': assert actual['realpath'] == edge['realpath']
    if is_project:
        group, _, row = project[child]
        obj = module_path((P if group == 'p72' else B)/'lib',child,'.olean')
        assert edge['sha256'] == row['object_sha256']
        assert actual['realpath'] == str(obj.resolve(strict=True))
observed_external = {n:[{'path':p,'realpath':r,'sha256':h} for p,r,h in sorted(v)] for n,v in sorted(external.items())}
assert observed_external == claim['external_bindings']
assert all(len(v) == 1 for v in external.values())
def list_sha(xs):
    return hashlib.sha256(json.dumps(sorted(xs),separators=(',',':')).encode()).hexdigest()
assert claim['external_leaves_sha256'] == list_sha(external)
assert claim['reached_modules_sha256'] == list_sha(visited)
assert claim['reached_p72_row_files_sha256'] == list_sha(
    str(files[project[n][1]]) + ':' + sha(files[project[n][1]])
    for n in visited if project[n][0] == 'p72')
assert claim['distinct_files_hashed'] == len(cache)
counts = {'seeds':len(seeds), 'reached_p72_producers':sum(project[n][0] == 'p72' for n in visited),
 'reached_base_producers':sum(project[n][0] == 'base' for n in visited), 'recorded_edges':len(edges),
 'external_leaf_names':len(external), 'distinct_guard_slots_checked':len(slots),
 'guard_slots_present':sum(v is not None for v in slots.values()),
 'guard_slots_absent':sum(v is None for v in slots.values())}
assert all(claim[key] == value for key,value in counts.items())
assert claim['base_link_objects_checked'] == counts['reached_base_producers']
assert claim['mismatches'] == []
print(json.dumps({'scope':'independent recorded-edge, source/object/link and recorded-slot checks; not Lean resolution or provider compatibility', **counts, 'unique_external_bindings':True, 'mismatches':0},indent=2,sort_keys=True))
