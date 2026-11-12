#!/usr/bin/env python3
"""Read-only recorded-edge closure audit; never invokes Lean or writes evidence."""
import hashlib
import json
import os
import sys
from pathlib import Path

if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):
    raise SystemExit('Use python3 -I -S -B')

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
    D/'research/ordinary14-natural79-corrected-ordered-provider-plan/plan.json': 'deb0854620b8fb85461df791c545f43c09814b566ec4685517efa1696d46b035',
    D/'research/ordinary14-natural80-recorded-ancestry-audit/observation.json': '865b64695a9195dd460f43dbbf1b3ec72cdf50503b0fbbd4de4e4c1c1186d25c',
    D/'research/ordinary14-root74-provider-survey/observation.json': '14732a54d8f2d3592d31f78d731497a1d804780ca8ec643e3851314868e7b4ab',
    D/'research/ordinary14-natural80-qualified-provider-cut/observation.json': 'c88630304b866b29fe68a11f14f44af210fcd8ea5eed173523ae687c8c157979',
    D/'research/ordinary14-root74-recorded-ancestry-audit/observation.json': '1c1a1afcb7fafe99d1544b714946adb3a2847032edf00923305ec4da47593c0a',
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
front80 = sorted(load(D/'research/ordinary14-natural80-qualified-provider-cut/observation.json')['selected_project_frontier'])
plan = load(D/'research/ordinary14-natural79-corrected-ordered-provider-plan/plan.json')
front = sorted(plan['selected_project_frontier_sources_and_objects'])
assert len(front80) == len(set(front80)) == 40 and len(front) == len(set(front)) == 41
new_seed = 'DiophantineConsistency.Compact44.ReducedNormSigned'
assert set(front)-set(front80) == {new_seed} and set(front80) <= set(front)
assert new_seed in rows and rows[new_seed]['index'] == 69
for n in front:
    recorded = plan['selected_project_frontier_sources_and_objects'][n]
    source = D/'Lean'/Path(*n.split('.')).with_suffix('.lean')
    obj = P/'lib'/Path(*n.split('.')).with_suffix('.olean')
    assert str(source) == recorded['source']['path'] and str(source.resolve(strict=True)) == recorded['source']['realpath']
    assert str(obj) == recorded['object']['path'] and str(obj.resolve(strict=True)) == recorded['object']['realpath']
    assert digest(source) == recorded['source']['sha256']
    assert digest(obj) == recorded['object']['sha256']
    assert rows.get(n,records.get(n))['source_sha256'] == recorded['source']['sha256']
    assert rows.get(n,records.get(n))['object_sha256'] == recorded['object']['sha256']


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

# Independently replay reachability from the 40 earlier seeds within the
# observed recorded edges. The additional natural79 seed turn out to
# lie in that same recorded project closure. This says nothing about imports
# omitted from the records or Lean's actual runtime resolution.
children = {n:[] for n in seen}
for parent,child,edge,kind,is_project in edges:
    if is_project: children[parent].append(child)
old_todo,old_seen=list(front80),set()
while old_todo:
    n=old_todo.pop()
    if n in old_seen: continue
    old_seen.add(n);old_todo.extend(children[n])
assert old_seen==seen

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
assert not errors,errors
prior=load(D/'research/ordinary14-natural80-recorded-ancestry-audit/observation.json')
assert prior['reached_modules_sha256']==list_hash(seen)
assert prior['external_leaves_sha256']==list_hash(external)
assert prior['reached_p72_row_files_sha256']==list_hash(str(rowfile[n])+':'+digest(rowfile[n]) for n in seen if n in rows)
assert prior['external_bindings']==external_bindings
assert prior['reached_p72_producers']==len(seen & set(rows))
assert prior['reached_base_producers']==len(seen & set(records))
assert prior['recorded_edges']==len(edges)
assert prior['distinct_files_hashed']==len(files_cache)
assert prior['distinct_guard_slots_checked']==len(slots_cache)
assert prior['guard_slots_present']==sum(v is not None for v in slots_cache.values())
assert prior['guard_slots_absent']==sum(v is None for v in slots_cache.values())
assert prior['mismatches']==[]
new_row = rows[new_seed]
assert new_seed in old_seen
print(json.dumps({
    'scope':'point-in-time recorded project-edge closure from 41 corrected natural79 lexical frontier seeds; not Lean resolution or complete provider coherence',
    'seeds':len(front), 'added_seeds_vs_natural80':sorted(set(front)-set(front80)),
    'omitted_seeds_vs_natural80':sorted(set(front80)-set(front)),
    'new_seed_in_natural80_recorded_closure':new_seed in old_seen,
    'natural80_recorded_project_closure_identical':old_seen==seen,
    'additional_recorded_project_ancestors':sorted(seen-old_seen),
    'new_seed_recorded_p72_row':{'module':new_seed,'index':new_row['index'],
       'row_file':str(rowfile[new_seed]),'row_sha256':digest(rowfile[new_seed]),
       'source_sha256':new_row['source_sha256'],'object_sha256':new_row['object_sha256'],
       'recorded_direct_dependencies':new_row['dependencies'],'recorded_direct_guard_slots':len(new_row['direct_guard'])},
    'reached_p72_producers':len(seen & set(rows)), 'reached_base_producers':len(seen & set(records)),
    'recorded_edges':len(edges), 'external_leaf_names':len(external), 'external_leaves_sha256':list_hash(external),
    'external_bindings':external_bindings, 'reached_modules_sha256':list_hash(seen),
    'reached_p72_row_files_sha256':list_hash(str(rowfile[n])+':'+digest(rowfile[n]) for n in seen if n in rows),
    'base_link_objects_checked':len(seen & set(records)), 'distinct_files_hashed':len(files_cache),
    'distinct_guard_slots_checked':len(slots_cache),
    'guard_slots_present':sum(v is not None for v in slots_cache.values()),
    'guard_slots_absent':sum(v is None for v in slots_cache.values()), 'mismatches':errors,
    'limitations':'recorded direct edges only; P72 row hashes except the final row are observations, not independently anchored; no package-transitive/runtime/implicit closure, atomic snapshot, Lean invocation or compatibility theorem'
},indent=2,sort_keys=True))
