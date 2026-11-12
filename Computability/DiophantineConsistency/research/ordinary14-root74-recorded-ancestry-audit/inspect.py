#!/usr/bin/env python3
"""Read-only recorded-edge closure audit; never invokes Lean or writes evidence."""
import hashlib
import json
import os
from pathlib import Path

D = Path(__file__).resolve().parents[2]
P = Path('/tmp/p72-current-base-extension-attempt02-20261105')
B = Path('/tmp/current14-standard-fresh-build-20261104')
S = Path('/tmp/current14-standard-fresh-source-20261104')

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''): h.update(chunk)
    return h.hexdigest()

pins = {
    D/'research/ordinary14-root74-provider-survey/observation.json': '14732a54d8f2d3592d31f78d731497a1d804780ca8ec643e3851314868e7b4ab',
    P/'progress.json':'f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a',
    P/'source-snapshot.json':'4536c44c399dc42037b692a39a36cc74c807693e1e5a76e2f5db299691fff7d8',
    P/'base-links.json':'16aa5524fd4e6fc65acd557a1e644d077e8dc70835c408411f5d5ae9597bfe24',
    B/'state.json':'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014',
    S/'manifest.json':'1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749',
}
for path, h in pins.items(): assert digest(path) == h, str(path)
load = lambda p: json.loads(p.read_text())
progress, snapshot, links, base = (load(P/'progress.json'),load(P/'source-snapshot.json'),
                                    load(P/'base-links.json'),load(B/'state.json'))
assert progress['status'] == base['status'] == 'PASS'
assert progress['source_snapshot_sha256'] == pins[P/'source-snapshot.json']
assert progress['base_links_sha256'] == pins[P/'base-links.json']
assert base['manifest_sha256'] == pins[S/'manifest.json']
files = sorted((P/'rows').glob('[0-9][0-9][0-9][0-9].json'))
assert len(files) == progress['completed'] == progress['total'] == len(snapshot) == 681
rows = {}
rowfile = {}
for f in files:
    r = load(f)
    assert r['module'] not in rows and r['status'] == 'PASS'
    assert f.name == f"{r['index']:04d}.json"
    rows[r['module']], rowfile[r['module']] = r, f
assert digest(files[-1]) == progress['last_row_sha256']
records = {r['module']:r for r in base['records']}
assert len(records) == len(base['records']) == 1000
assert not set(rows) & set(records)
indices = {r['module']:i for i,r in enumerate(base['records'])}
front = load(D/'research/ordinary14-root74-provider-survey/observation.json')['slim_cut_frontier']
assert len(front) == len(set(front)) == 31

# Follow only recorded direct edges. This is neither Lean resolution nor an
# external/package-transitive or implicit/runtime dependency traversal.
todo, seen, external, edges = list(front), set(), set(), []
while todo:
    n = todo.pop()
    if n in seen: continue
    seen.add(n)
    assert n in rows or n in records, n
    if n in rows:
        r = rows[n]
        for child, edge in r['dependencies'].items():
            is_project = child in rows or child in records
            if is_project:
                if child in rows: assert rows[child]['index'] < r['index'], (n,child)
                todo.append(child)
            else: external.add(child)
            edges.append((n,child,edge,'p72',is_project))
    else:
        r = records[n]
        assert r['exit'] == 0
        for child, edge in r['direct_inputs'].items():
            assert edge['kind'] in ('project','package')
            is_project = edge['kind'] == 'project'
            if is_project:
                assert child in records and indices[child] < indices[n], (n,child)
                todo.append(child)
            else: external.add(child)
            edges.append((n,child,edge,'base',is_project))

errors = []
files_cache, slots_cache = {}, {}
def observed(path):
    key = str(path)
    if key not in files_cache:
        try:
            real = str(path.resolve(strict=True))
            files_cache[key] = {'realpath':real,'sha256':digest(Path(real))}
        except OSError as e:
            files_cache[key] = {'error':type(e).__name__}
    return files_cache[key]
def compare(label, actual, expected):
    if actual != expected: errors.append({'label':label,'actual':actual,'expected':expected})
def slot(path):
    key = str(path)
    if key not in slots_cache:
        slots_cache[key] = observed(path) if os.path.lexists(path) else None
    return slots_cache[key]

for n in sorted(seen):
    if n in rows:
        r = rows[n]
        assert snapshot[n] == r['source_sha256']
        source = P/'src'/Path(*n.split('.')).with_suffix('.lean')
        obj = P/'lib'/Path(*n.split('.')).with_suffix('.olean')
    else:
        r = records[n]
        source = S/'src'/Path(*n.split('.')).with_suffix('.lean')
        obj = B/'lib'/Path(*n.split('.')).with_suffix('.olean')
    compare(n+' source_sha256', observed(source).get('sha256'), r['source_sha256'])
    compare(n+' object_sha256', observed(obj).get('sha256'), r['object_sha256'])
    if n in records:
        linked = P/'lib'/Path(*n.split('.')).with_suffix('.olean')
        compare(n+' recorded_base_link', links.get(str(linked)), str(obj))
        compare(n+' current_link_target', str(linked.resolve(strict=True)),str(obj.resolve(strict=True)))
        assert linked.is_symlink()
        for path, expected in base['outputs'][n].items():
            compare('base output '+path, slot(Path(path)), expected)
    else:
        for path, expected in r['direct_guard'].items():
            compare('p72 direct_guard '+path, slot(Path(path)), expected)

for parent, child, edge, kind, is_project in edges:
    actual = observed(Path(edge['path']))
    compare(parent+' -> '+child+' edge sha256', actual.get('sha256'), edge['sha256'])
    if kind == 'p72': compare(parent+' -> '+child+' edge realpath',actual.get('realpath'),edge['realpath'])
    if is_project:
        producer = rows[child] if child in rows else records[child]
        compare(parent+' -> '+child+' producer hash', edge['sha256'],producer['object_sha256'])
        root = P if child in rows else B
        expected = root/'lib'/Path(*child.split('.')).with_suffix('.olean')
        compare(parent+' -> '+child+' producer realpath',actual.get('realpath'),str(expected.resolve(strict=True)))

assert all(n == 'Init' or n.startswith(('Foundation.','Mathlib.','Lean.')) for n in external)
bindings = {n:set() for n in external}
for parent,child,edge,kind,is_project in edges:
    if not is_project:
        obs = observed(Path(edge['path']))
        bindings[child].add((edge['path'],obs.get('realpath'),edge['sha256']))
external_bindings = {n:[{'path':p,'realpath':r,'sha256':h} for p,r,h in sorted(values)]
                     for n,values in sorted(bindings.items())}
def list_hash(items):
    return hashlib.sha256(json.dumps(sorted(items),separators=(',',':')).encode()).hexdigest()
print(json.dumps({
    'scope':'point-in-time recorded project-edge closure from 31 lexical frontier seeds; not Lean resolution or complete provider coherence',
    'seeds':len(front), 'reached_p72_producers':len(seen & set(rows)),
    'reached_base_producers':len(seen & set(records)), 'recorded_edges':len(edges),
    'external_leaf_names':len(external), 'external_leaves_sha256':list_hash(external),
    'external_bindings':external_bindings,
    'reached_modules_sha256':list_hash(seen),
    'reached_p72_row_files_sha256':list_hash(str(rowfile[n])+':'+digest(rowfile[n]) for n in seen if n in rows),
    'base_link_objects_checked':len(seen & set(records)), 'distinct_files_hashed':len(files_cache),
    'distinct_guard_slots_checked':len(slots_cache),
    'guard_slots_present':sum(v is not None for v in slots_cache.values()),
    'guard_slots_absent':sum(v is None for v in slots_cache.values()), 'mismatches':errors,
    'limitations':'recorded direct edges only; P72 row hashes except the final row are observations, not independently anchored; no package-transitive/runtime/implicit closure, atomic snapshot, Lean invocation or compatibility theorem'
},indent=2,sort_keys=True))
