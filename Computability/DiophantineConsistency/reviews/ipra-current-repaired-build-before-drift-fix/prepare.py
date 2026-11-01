#!/usr/bin/env python3
"""Freeze inputs for the source-survey rebuild; this does not run Lean."""
from pathlib import Path
import hashlib
import json
import os

D = Path(__file__).resolve().parent
R = D.parents[3]
V = R / 'Computability/DiophantineConsistency/reviews'
SURVEY = V / 'ipra-current-repaired-survey'
P14 = V / 'ipra-current-native14-repaired-replay'
PLAN = V / 'ipra-frozen-repair-plan-v2/manifest.json'
OUT = V / 'ipra-current-repaired-build'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
A = Path('/tmp/ipra-frozen-ancestry-repair-5_g68wg3')
B = Path('/tmp/ipra-frozen-ancestry-repair-6ftdeyrq')
ORIG = V / 'ipra-frozen-repair-plan-v2-verification/receipt.json'
CMP = V / 'ipra-frozen-repair-v2-verification/receipt.json'
CMP2 = V / 'ipra-frozen-repair-v2-verification-fourth/receipt.json'
CL = V / 'ipra-frozen-repair-plan-v2-closure-audit/receipt.json'
SO = V / 'ipra-frozen-repair-plan-v2-source-origin-audit/receipt.json'
SIDECARS = ('.olean', '.olean.private', '.olean.server', '.ir', '.olean.hash',
            '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean', '.ilean.hash')

def digest(b):
    return hashlib.sha256(b).hexdigest()

def h(path):
    return digest(Path(path).read_bytes())

gate = {}
def read(path):
    path = Path(path).absolute()
    assert path.resolve() == path, ('noncanonical gate', str(path))
    raw = path.read_bytes()
    val = digest(raw)
    assert str(path) not in gate or gate[str(path)] == val
    gate[str(path)] = val
    return json.loads(raw), val

def pin(path, expected):
    path = Path(path).absolute()
    assert path.resolve() == path, ('noncanonical gate', str(path))
    assert h(path) == expected, ('digest mismatch', str(path))
    assert str(path) not in gate or gate[str(path)] == expected
    gate[str(path)] = expected

def inventory(root):
    result = {}
    for directory, _, files in os.walk(root / 'lib', followlinks=True):
        for name in files:
            if name.endswith(SIDECARS):
                p = Path(directory) / name
                result[str(p.relative_to(root / 'lib'))] = {
                    'sha256': h(p), 'resolved_path': str(p.resolve())}
    return result

def audit_external(m):
    for name, info in m['external'].items():
        assert info['selected'] in {v['realpath'] for v in info['companions'].values() if v}
        for path, item in info['companions'].items():
            if item is None:
                assert not os.path.lexists(path), ('unexpected external companion', name, path)
            else:
                assert str(Path(path).resolve()) == item['realpath'] and h(path) == item['sha256'], (name, path)

def audit_plan_external(f):
    assert set(f['external_direct_paths']) == set(f['external_resolved_paths'])
    for path, sha in f['external_direct_paths'].items():
        assert h(path) == sha and str(Path(path).resolve()) == f['external_resolved_paths'][path], path
    assert all(not os.path.lexists(p) for p in f['external_absent_paths'])

def drift(m):
    result = []
    for n, rec in m['sources'].items():
        path = R / rec['path']
        if not path.is_file() or h(path) != rec['sha256']:
            result.append(n)
    return sorted(result)

def audit_snapshots(m):
    for n, rec in m['sources'].items():
        path = SURVEY / 'sources' / (n.replace('.', '/') + '.lean')
        assert path.is_file() and not path.is_symlink() and path.resolve() == path.absolute()
        assert h(path) == rec['sha256'], n

assert not OUT.exists(), ('refusing to overwrite', str(OUT))
prep = Path(__file__).read_bytes()
driver = (D / 'replay.py').read_bytes()
survey, survey_h = read(SURVEY / 'manifest.json')
deps, deps_h = read(SURVEY / 'lean-deps-receipt.json')
closure, closure_h = read(SURVEY / 'closure-receipt.json')
plan, plan_h = read(PLAN)
previous, previous_h = read(P14 / 'manifest.json')
author, author_h = read(A / 'state.json')
peer, peer_h = read(B / 'state.json')
orig, orig_h = read(ORIG)
cmp, cmp_h = read(CMP)
at, at_h = read(CMP.parent / 'terminal.json')
cmp2, cmp2_h = read(CMP2)
ct, ct_h = read(CMP2.parent / 'terminal.json')
cl, cl_h = read(CL)
so, so_h = read(SO)
st, st_h = read(SO.parent / 'terminal.json')

assert survey['parent'] == str(B) and survey['parent_state_sha256'] == peer_h
assert previous['peer'] == str(B) and previous['peer_state_sha256'] == peer_h
assert previous['author'] == str(A) and previous['author_state_sha256'] == author_h
assert survey['repair_plan_sha256'] == plan_h == previous['frozen_13_manifest_sha256']
assert peer['status'] == author['status'] == 'PASS'
assert peer['manifest_sha256'] == author['manifest_sha256'] == plan_h
assert peer['driver_sha256'] == author['driver_sha256'] == plan['driver_sha256']
assert [x['name'] for x in author['records']] == [x['name'] for x in peer['records']] == plan['order']
assert len(plan['order']) == 73
assert orig['status'] == 'MATCHED_PLAN' and orig['author_manifest_sha256'] == plan_h and orig['replay_sha256'] == plan['driver_sha256']
assert cmp['status'] == 'MATCHED_PASS' and cmp['manifest_sha256'] == plan_h and cmp['rows'] == 73
assert cmp['author_state_sha256'] == author_h and cmp['peer_state_sha256'] == peer_h
assert cmp2 == cmp and cmp2_h == cmp_h
assert at['status'] == 'PASS_EXIT_0' and at['exit_code'] == 0 and at['receipt_sha256'] == cmp_h and at['compare_sha256'] == cmp['compare_sha256']
assert ct['status'] == 'PASS_EXIT_0' and ct['exit_code'] == 0 and ct['receipt_sha256'] == cmp2_h and ct['author_receipt_sha256'] == cmp_h and ct['before'] == ct['after']
assert cl['status'] == 'PASS_PROJECT_CLOSURE' and cl['plan_manifest_sha256'] == plan_h and cl['fixed_manifest_sha256'] == plan['fixed_manifest_sha256']
assert so['status'] == 'PASS_PROJECT_SOURCE_ORIGINS' and so['plan_manifest_sha256'] == plan_h and so['fixed_manifest_sha256'] == plan['fixed_manifest_sha256']
assert st['status'] == 'PASS_EXIT_0' and st['exit_code'] == 0 and st['receipt_sha256'] == so_h and st['audit_sha256'] == so['audit_sha256'] and st['source_nodes_sha256'] == so['source_nodes_sha256']
for field, actual in [('parent_origin_receipt_sha256', orig_h), ('parent_comparison_receipt_sha256', cmp_h),
                      ('parent_comparison_author_terminal_sha256', at_h), ('parent_comparison_peer_receipt_sha256', cmp2_h),
                      ('parent_comparison_terminal_sha256', ct_h), ('parent_closure_receipt_sha256', cl_h),
                      ('parent_source_origin_receipt_sha256', so_h), ('parent_source_origin_terminal_sha256', st_h)]:
    assert previous[field] == actual, field
assert previous['parent_origin_guard'] == plan['origin_guard']
for field in ('external_direct_paths', 'external_resolved_paths', 'external_absent_paths'):
    assert previous['parent_' + field] == plan[field], field
for path, sha in previous['parent_receipt_checker_guard'].items():
    pin(path, sha)
pin(SURVEY / 'survey.py', survey['surveyor_sha256'])
pin(V / 'ipra-adaptive-native-current-rebase/manifest.json', survey['old_manifest_sha256'])
pin(SURVEY / 'check_lean_deps.py', deps['checker_sha256'])
pin(SURVEY / 'check_closure.py', closure['checker_sha256'])
pin(P14 / 'prepare.py', previous['preparer_sha256'])
pin(P14 / 'replay.py', previous['driver_sha256'])
pin(Path(previous['ancestor_state']), previous['ancestor_state_sha256'])
for path, sha in previous['ancestral_manifests'].items():
    pin(path, sha)
assert deps['manifest_sha256'] == closure['manifest_sha256'] == survey_h
assert deps['lean_sha256'] == previous['lean_sha256'] == plan['lean_sha256'] == h(LEAN)
assert deps['count'] == len(deps['rows']) == len(survey['sources']) == 1099 and deps['errors'] == {}
assert set(deps['rows']) == set(survey['sources'])
assert closure['status'] == 'PASS' and closure['sources'] == 1099 and closure['rebuild'] == 258
assert closure['selected_project_objects'] == len(survey['selected_project_objects']) == 1098
assert closure['direct_external_modules'] == len(survey['external']) == 106
assert len(survey['order']) == len(set(survey['order'])) == 258
assert survey['order'][-1] == survey['target']
indices = {n: i for i, n in enumerate(survey['order'])}
assert set(indices) <= survey['sources'].keys()
audit_snapshots(survey)
for n, rec in survey['sources'].items():
    if n in indices:
        for dep in rec['imports']:
            if dep in indices:
                assert indices[dep] < indices[n], (n, dep)
for n, obj in survey['selected_project_objects'].items():
    rel = n.replace('.', '/') + '.olean'
    assert previous['parent_inventory'][rel] == {'sha256': obj['sha256'], 'resolved_path': obj['path']}, n
for x, y in zip(author['records'], peer['records']):
    assert all(x.get(k) == y.get(k) for k in ('name', 'exit', 'object_sha256', 'log_sha256', 'warnings')) and x['exit'] == 0
    assert {n: v['sha256'] for n, v in x['direct_imports'].items()} == {n: v['sha256'] for n, v in y['direct_imports'].items()}
    for root, row in ((A, x), (B, y)):
        obj = root / 'lib' / (row['name'].replace('.', '/') + '.olean')
        assert obj.is_file() and not obj.is_symlink() and obj.resolve() == obj.absolute() and h(obj) == row['object_sha256']
        pin(obj, row['object_sha256'])
        pin(root / 'logs' / (row['name'].replace('.', '_') + '.log'), row['log_sha256'])
        for v in row['direct_imports'].values():
            pin(v['resolved_path'], v['sha256'])

before_drift = drift(survey)
assert inventory(B) == previous['parent_inventory']
assert all(h(path) == sha for path, sha in plan['origin_guard'].items())
audit_plan_external(plan)
audit_external(survey)
assert all(str(Path(path).resolve()) == path and h(path) == sha for path, sha in gate.items())
audit_snapshots(survey)
after_drift = drift(survey)
assert inventory(B) == previous['parent_inventory']
assert all(h(path) == sha for path, sha in plan['origin_guard'].items())
audit_plan_external(plan)
audit_external(survey)
assert all(str(Path(path).resolve()) == path and h(path) == sha for path, sha in gate.items())
assert h(__file__) == digest(prep) and h(D / 'replay.py') == digest(driver) and h(LEAN) == plan['lean_sha256']

manifest = {
    'survey_manifest_path': str((SURVEY / 'manifest.json').absolute()),
    'survey_manifest_sha256': survey_h,
    'parent_state_path': str(B / 'state.json'), 'parent_state_sha256': peer_h,
    'parent_inventory': previous['parent_inventory'], 'gate_guard': gate,
    'origin_guard': plan['origin_guard'],
    'parent_external_direct_paths': plan['external_direct_paths'],
    'parent_external_resolved_paths': plan['external_resolved_paths'],
    'parent_external_absent_paths': plan['external_absent_paths'],
    'lean_sha256': plan['lean_sha256'], 'driver_sha256': digest(driver),
    'preparer_sha256': digest(prep),
    'workspace_drift_before': before_drift, 'workspace_drift_after': after_drift,
    'boundary': 'Fixed survey source snapshot on matched 73-module repaired parent. Source-current status requires independently verifying all captured workspace source paths against the snapshot at the start and end of replay. The 848-project ancestor is author-only; external package-transitive and dynamic ancestry remain inherited.'}
assert not OUT.exists(), ('refusing to overwrite', str(OUT))
OUT.mkdir()
(OUT / 'prepare.py').write_bytes(prep)
(OUT / 'replay.py').write_bytes(driver)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
print('PASS_INPUT', 'sources', len(survey['sources']), 'rebuild', len(survey['order']),
      'driver', manifest['driver_sha256'], 'manifest', h(OUT / 'manifest.json'),
      'workspace_drift_before', len(before_drift), 'workspace_drift_after', len(after_drift))
