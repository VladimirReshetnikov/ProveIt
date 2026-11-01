#!/usr/bin/env python3
"""Provisional, fail-closed preparer for a source-directed 107-parent rebase.

Run from repository root: prepare.py SURVEY_DIR OUTPUT_DIR. No proof is run here.
"""
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import sys

if len(sys.argv) != 3:
    raise SystemExit('usage: prepare.py CANDIDATE_SURVEY_DIR OUTPUT_DIR')
SUR = Path(sys.argv[1]).resolve()
OUT = Path(sys.argv[2]).absolute()
R = Path.cwd().resolve()
V = R / 'Computability/DiophantineConsistency/reviews'
P258 = V / 'ipra-current-repaired-six-drift-replay'
S258 = V / 'ipra-current-repaired-six-drift-source-survey'
ORIGSUR = V / 'ipra-current-repaired-survey'
S7 = V / 'ipra-current-repaired-seven-drift-source-survey'
S8 = V / 'ipra-current-repaired-eight-drift-source-survey'
F73 = V / 'ipra-frozen-repair-plan-v2/manifest.json'
OLD = V / 'ipra-adaptive-native-current-rebase/manifest.json'
O = V / 'ipra-current-repaired-six-drift-terminal-observations'
CA = V / 'ipra-current-repaired-six-drift-verification'
CB = V / 'ipra-current-repaired-six-drift-verification-peer'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PKG = Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
TOOL = LEAN.parent.parent / 'lib/lean'
SIDECARS = ('.olean','.olean.private','.olean.server','.ir','.olean.hash',
            '.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
gate = {}
def pin(path, expected=None):
    p = Path(path).absolute()
    assert p.is_file() and p.resolve() == p, ('noncanonical gate', str(p))
    h = H(p)
    assert expected is None or h == expected, ('digest mismatch', str(p))
    assert str(p) not in gate or gate[str(p)] == h
    gate[str(p)] = h
    return h
def read(path):
    pin(path)
    return json.loads(Path(path).read_text())
def inventory(root):
    out = {}
    for d, _, files in os.walk(root / 'lib', followlinks=True):
        for name in files:
            if name.endswith(SIDECARS):
                p = Path(d) / name
                out[str(p.relative_to(root / 'lib'))] = {'sha256': H(p), 'resolved_path': str(p.resolve())}
    return out
def external(s, m):
    assert set(m['parent_external_direct_paths']) == set(m['parent_external_resolved_paths'])
    for path, h in m['parent_external_direct_paths'].items():
        assert H(path) == h and str(Path(path).resolve()) == m['parent_external_resolved_paths'][path]
    assert all(not os.path.lexists(path) for path in m['parent_external_absent_paths'])
    for name, row in s['external'].items():
        rel = name.replace('.', '/') + '.olean'
        selected = next((p for p in (PKG / rel, TOOL / rel) if p.is_file()), None)
        assert selected is not None and str(selected.resolve()) == row['selected'], name
        for path, item in row['companions'].items():
            if item is None:
                assert not os.path.lexists(path), path
            else:
                assert Path(path).is_file() and str(Path(path).resolve()) == item['realpath'] and H(path) == item['sha256'], path
def observation(path, field, expected_path, expected_hash):
    row = read(path)
    assert row['status'] == 'PASS_EXIT_0' and row['exit_code'] == 0
    assert row['evidence_kind'] == 'tool_session_observation' and row['session_id']
    assert row[field + '_path'] == str(expected_path) and row[field + '_sha256'] == expected_hash
    return row

def comparison(directory, wrapper_observation):
    receipt = read(directory / 'receipt.json')
    terminal = read(directory / 'terminal.json')
    assert receipt['status'] == 'MATCHED_PASS' and receipt['rows'] == 107
    assert terminal['status'] == 'PASS_COMPARATOR_EXIT_0' and terminal['comparator_exit_code'] == 0
    assert terminal['before'] == terminal['after']
    assert terminal['receipt_sha256'] == H(directory / 'receipt.json')
    assert receipt['compare_sha256'] == pin(directory / 'compare.py')
    pin(directory / 'run.py', terminal['before'][str((directory / 'run.py').resolve())])
    pin(directory / 'run.log', terminal['log_sha256'])
    for path, h in terminal['before'].items():
        pin(path, h)
    assert (directory / 'run.log').read_text() == (
        f"MATCHED_PASS 107 rows {receipt['guarded_file_count']} files "
        f"workspace_matches {receipt['workspace_matches_snapshot_through_observations']}\n")
    observation(wrapper_observation, 'terminal', directory / 'terminal.json', H(directory / 'terminal.json'))
    return receipt

assert not OUT.exists(), ('refusing to overwrite', str(OUT))
prep = Path(__file__).read_bytes()
driver = (Path(__file__).resolve().parent / 'replay.py').read_bytes()
new = read(SUR / 'manifest.json')
old = read(S258 / 'manifest.json')
m258 = read(P258 / 'manifest.json')
f73 = read(F73)
old_sources = read(OLD)
ra = comparison(CA, O / 'author-comparison.json')
rb = comparison(CB, O / 'peer-comparison.json')
assert ra == rb and H(CA / 'receipt.json') == H(CB / 'receipt.json')
assert ra['manifest_sha256'] == H(P258 / 'manifest.json')
assert ra['driver_sha256'] == m258['driver_sha256'] == pin(P258 / 'replay.py')
assert ra['survey_manifest_sha256'] == m258['candidate_survey_sha256'] == H(S258 / 'manifest.json')
pin(P258 / 'prepare.py', m258['preparer_sha256'])
A, B = Path(ra['author_path']), Path(ra['peer_path'])
assert A.resolve() != B.resolve() and not os.path.samefile(A / 'state.json', B / 'state.json')
a, b = read(A / 'state.json'), read(B / 'state.json')
ah, bh = H(A / 'state.json'), H(B / 'state.json')
assert ah == ra['author_state_sha256'] and bh == ra['peer_state_sha256']
assert a['status'] == b['status'] == 'PASS'
assert a['manifest_sha256'] == b['manifest_sha256'] == ra['manifest_sha256']
assert a['driver_sha256'] == b['driver_sha256'] == ra['driver_sha256']
observation(O / 'author.json', 'state', A / 'state.json', ah)
observation(O / 'peer.json', 'state', B / 'state.json', bh)
assert [x['name'] for x in a['records']] == [x['name'] for x in b['records']] == old['order']
assert len(old['order']) == 107
orig = read(ORIGSUR / 'manifest.json')
assert H(F73) == orig['repair_plan_sha256']
st73 = read(Path(orig['parent']) / 'state.json')
assert st73['status'] == 'PASS' and H(Path(orig['parent']) / 'state.json') == orig['parent_state_sha256']
st258 = read(Path(m258['parent_state_path']))
assert st258['status'] == 'PASS' and H(Path(m258['parent_state_path'])) == m258['parent_state_sha256']
assert H(LEAN) == m258['lean_sha256']
for path, h in m258['gate_guard'].items(): pin(path, h)
for path, h in m258['origin_guard'].items(): pin(path, h)

assert len(new['sources']) == len(old['sources']) == 1099
assert set(new['sources']) == set(old['sources'])
assert new['target'] == old['target'] and new['external'] == old['external']
seeds = set()
for name, row in new['sources'].items():
    prev = old['sources'][name]
    assert row['path'] == prev['path']
    if row['sha256'] == prev['sha256']:
        assert row['imports'] == prev['imports'], ('unchanged source import mismatch', name)
    if row['sha256'] != prev['sha256']:
        seeds.add(name)
    for root, expected in ((SUR / 'sources', row['sha256']), (S258 / 'sources', prev['sha256'])):
        src = root / (name.replace('.', '/') + '.lean')
        assert src.is_file() and not src.is_symlink() and src.resolve() == src.absolute()
        assert H(src) == expected, (name, str(src))
        pin(src, expected)

# Retained source nodes outside the candidate source graph can still be in
# historical project environments; fail closed if any of these five drift.
extra_workspace = {}
for name in set(f73['source_sha256']) - set(new['sources']):
    path = R / old_sources['source_files'][name]
    assert path.is_file() and H(path) == f73['source_sha256'][name], ('old environment source drift', name)
    extra_workspace[name] = {'path': str(path.relative_to(R)), 'sha256': f73['source_sha256'][name]}
assert len(extra_workspace) == 5

# Pin the inherited 1,099-source parser audit, the six edited-header audit,
# and the two subsequent one-header Lean parser receipts and all their inputs.
origdeps=read(ORIGSUR/'lean-deps-receipt.json');sixdeps=read(S258/'lean-deps-receipt.json')
sevendeps=read(S7/'lean-deps-receipt.json');eightdeps=read(S8/'lean-deps-receipt.json');elevendeps=read(SUR/'lean-deps-receipt.json')
assert origdeps['count']==len(origdeps['rows'])==1099 and not origdeps['errors']
assert origdeps['manifest_sha256']==H(ORIGSUR/'manifest.json') and origdeps['lean_sha256']==H(LEAN)
pin(ORIGSUR/'check_lean_deps.py',origdeps['checker_sha256'])
assert sixdeps['status']=='PASS_HEADER_DEPS' and len(sixdeps['rows'])==6
six_changed={n for n in old['sources'] if old['sources'][n]['sha256']!=orig['sources'][n]['sha256']}
assert set(sixdeps['rows'])==six_changed and len(six_changed)==6
for n in set(old['sources'])-six_changed:
    assert old['sources'][n]['imports']==orig['sources'][n]['imports']
for path,h in sixdeps['input_sha256'].items():pin(path,h)
assert sixdeps['input_sha256'][str((S258/'manifest.json').absolute())]==H(S258/'manifest.json')
for name,row in sixdeps['rows'].items():
    assert hashlib.sha256(row['stdout'].encode()).hexdigest()==row['stdout_sha256']
    modules=set()
    for line in row['stdout'].splitlines():
        path=Path(line);roots=(Path('/tmp/ipra-current-repaired-build-y6kamkla/lib'),PKG,TOOL)
        rel=next((path.relative_to(root) for root in roots if path.is_relative_to(root)),None)
        assert rel is not None and str(rel).endswith('.olean'),(name,line)
        modules.add(str(rel)[:-len('.olean')].replace('/','.'))
    assert modules-{'Init'}==set(old['sources'][name]['imports'])-{'Init'}
for source,dep in ((S7,sevendeps),(S8,eightdeps)):
    assert dep['status']=='PASS_HEADER_DEPS' and dep['module'] in seeds
    for path,h in dep['input_sha256'].items():pin(path,h)
    assert dep['input_sha256'][str((source/'manifest.json').absolute())]==H(source/'manifest.json')
    source_survey=read(source/'manifest.json')
    assert source_survey['sources'][dep['module']]['sha256']==new['sources'][dep['module']]['sha256']
    assert source_survey['sources'][dep['module']]['imports']==new['sources'][dep['module']]['imports']
    assert hashlib.sha256(dep['stdout'].encode()).hexdigest()==dep['stdout_sha256']
    modules=set()
    for line in dep['stdout'].splitlines():
        path=Path(line)
        roots=(Path('/tmp/ipra-current-repaired-build-y6kamkla/lib'),Path('/tmp/ipra-six-drift-replay-42b7hj5k/lib'),PKG,TOOL)
        rel=next((path.relative_to(root) for root in roots if path.is_relative_to(root)),None)
        assert rel is not None and str(rel).endswith('.olean'),line
        modules.add(str(rel)[:-len('.olean')].replace('/','.'))
    assert modules-{'Init'}==set(new['sources'][dep['module']]['imports'])-{'Init'}
assert elevendeps['status']=='PASS_HEADER_DEPS' and set(elevendeps['rows']) | {sevendeps['module'],eightdeps['module']} == seeds
assert set(elevendeps['rows']).isdisjoint({sevendeps['module'],eightdeps['module']})
for path,h in elevendeps['input_sha256'].items():pin(path,h)
assert elevendeps['input_sha256'][str((SUR/'manifest.json').absolute())]==H(SUR/'manifest.json')
for name,row in elevendeps['rows'].items():
    assert hashlib.sha256(row['stdout'].encode()).hexdigest()==row['stdout_sha256']
    modules=set()
    for line in row['stdout'].splitlines():
        path=Path(line);roots=(Path('/tmp/ipra-current-repaired-build-y6kamkla/lib'),Path('/tmp/ipra-six-drift-replay-42b7hj5k/lib'),PKG,TOOL)
        rel=next((path.relative_to(root) for root in roots if path.is_relative_to(root)),None)
        assert rel is not None and str(rel).endswith('.olean'),(name,line)
        modules.add(str(rel)[:-len('.olean')].replace('/', '.'))
    assert modules-{'Init'}==set(new['sources'][name]['imports'])-{'Init'}
    assert row['count']==len(set(new['sources'][name]['imports'])-{'Init'})


# Conservatively include current source edges, all actual 107/258 peer direct
# inputs and every recorded 73-plan project environment, including nonselected
# variants. This is an overapproximation and cannot omit a recorded old edge.
rev=collections.defaultdict(set)
for name,row in new['sources'].items():
    for dep in row['imports']:rev[dep].add(name)
for state in (b,st258,st73):
    for row in state['records']:
        for dep in row['direct_imports']:rev[dep].add(row['name'])
for node in f73['origin_nodes'].values():
    for dep in node['project_environment']:rev[dep].add(node['module'])
# Match every retained 73-origin selected object, rather than trusting names.
old_records={row['name']:row for row in st73['records']}
nodes={(x['module'],x['sha256'],x['physical_path']):x for x in f73['origin_nodes'].values()}
for name in set(new['sources'])-set(orig['order']):
    obj=orig['selected_project_objects'].get(name);assert obj is not None
    if name in old_records:assert obj['sha256']==old_records[name]['object_sha256']
    else:assert (name,obj['sha256'],obj['path']) in nodes, ('untraced retained origin',name)
impacted=set(seeds);queue=list(seeds)
while queue:
    for owner in rev[queue.pop()]:
        if owner not in impacted:impacted.add(owner);queue.append(owner)
order=new['order'];assert len(order)==len(set(order)) and impacted<=set(new['sources']) and set(order)==impacted
assert set(seeds) and new['target'] in order and order[-1]==new['target']
seen=set()
for name in order:
    assert all(dep not in set(order) or dep in seen for dep in new['sources'][name]['imports'])
    actual=re.findall(r'^import\s+([A-Z][\w.]*)',(SUR/'sources'/(name.replace('.', '/')+'.lean')).read_text(),re.M)
    assert actual==new['sources'][name]['imports'];seen.add(name)
rebuilt=set(old['order'])

# Authenticate the two whole parent overlays and all rebuilt rows, not merely
# their overlapping immediate imports.
excluded = {n.replace('.', '/') + suffix for n in rebuilt for suffix in SIDECARS}
base = {k: v for k, v in m258['parent_inventory'].items() if k not in excluded}
expected_inventories = []
for root, state in ((A, a), (B, b)):
    inv = dict(base)
    pin(root / 'manifest.json', ra['manifest_sha256'])
    pin(root / 'driver.py', ra['driver_sha256'])
    for row in state['records']:
        name = row['name']
        assert row['exit'] == 0 and 'warnings' in row
        obj = root / 'lib' / (name.replace('.', '/') + '.olean')
        assert obj.is_file() and not obj.is_symlink() and obj.resolve() == obj.absolute()
        pin(obj, row['object_sha256'])
        pin(root / 'logs' / (name.replace('.', '_') + '.log'), row['log_sha256'])
        for info in row['direct_imports'].values(): pin(info['resolved_path'], info['sha256'])
        inv[name.replace('.', '/') + '.olean'] = {'sha256': row['object_sha256'], 'resolved_path': str(obj.absolute())}
    assert inventory(root) == inv
    expected_inventories.append(inv)
for x, y in zip(a['records'], b['records']):
    assert all(x.get(k) == y.get(k) for k in ('name','exit','object_sha256','log_sha256','warnings'))
    assert {k:v['sha256'] for k,v in x['direct_imports'].items()} == {k:v['sha256'] for k,v in y['direct_imports'].items()}
for name in new['sources']:
    rel = name.replace('.', '/') + '.olean'
    assert rel in expected_inventories[1] or name in set(order), ('missing selected parent', name)
external(old, m258)

# Explicitly guard all possible package/toolchain candidates and companions for
# rebuilt project names, including absent paths. Direct-import paths are also
# checked before Lean; undeclared dynamic ancestry remains inherited.
fallback = {}
for name in order:
    for root in (PKG, TOOL):
        for suffix in SIDECARS:
            path = (root / (name.replace('.', '/') + suffix)).absolute()
            if os.path.lexists(path):
                assert path.is_file(), str(path)
                fallback[str(path)] = {'sha256': H(path), 'realpath': str(path.resolve())}
            else:
                fallback[str(path)] = None

def audit_all():
    assert all(str(Path(path).resolve()) == path and H(path) == h for path,h in gate.items())
    assert inventory(A) == expected_inventories[0] and inventory(B) == expected_inventories[1]
    external(old, m258)
    for path,row in m258['fallback_companions'].items():
        if row is None: assert not os.path.lexists(path),path
        else: assert Path(path).is_file() and str(Path(path).resolve())==row['realpath'] and H(path)==row['sha256']
    for path, row in fallback.items():
        if row is None: assert not os.path.lexists(path), path
        else: assert Path(path).is_file() and str(Path(path).resolve()) == row['realpath'] and H(path) == row['sha256']
    assert H(__file__) == hashlib.sha256(prep).hexdigest()
    assert H(Path(__file__).resolve().parent / 'replay.py') == hashlib.sha256(driver).hexdigest()

def drift(workspace):
    result = []
    for name,row in workspace.items():
        path = R / row['path']
        try: actual = H(path) if path.is_file() else None
        except OSError: actual = None
        if actual != row['sha256']: result.append({'module': name, 'expected': row['sha256'], 'actual': actual})
    return result
workspace = dict(new['sources']) | extra_workspace
assert len(workspace) == 1104
before_drift = drift(workspace)
audit_all()
after_drift = drift(workspace)
audit_all()
assert not OUT.exists(), ('refusing to overwrite', str(OUT))
manifest = {'status':'PROVISIONAL_REBASE_INPUT', 'workspace_root':str(R),
            'candidate_survey_path':str((SUR / 'manifest.json').absolute()),
            'candidate_survey_sha256':H(SUR / 'manifest.json'),
            'snapshot_root':str((SUR / 'sources').absolute()),
            'parent_state_path':str(B / 'state.json'), 'parent_state_sha256':bh,
            'parent_inventory':expected_inventories[1], 'gate_guard':gate,
            'origin_guard':m258['origin_guard'],
            'parent_external_direct_paths':m258['parent_external_direct_paths'],
            'parent_external_resolved_paths':m258['parent_external_resolved_paths'],
            'parent_external_absent_paths':m258['parent_external_absent_paths'],
            'fallback_companions':fallback, 'inherited_fallback_companions':m258['fallback_companions'], 'workspace_sources':workspace,
            'changed_seeds':sorted(seeds), 'order':order, 'target':new['target'],
            'lean_sha256':m258['lean_sha256'], 'driver_sha256':hashlib.sha256(driver).hexdigest(),
            'preparer_sha256':hashlib.sha256(prep).hexdigest(),
            'workspace_drift_before':before_drift, 'workspace_drift_after':after_drift,
            'parent_comparison_receipts':[str((CA/'receipt.json').absolute()),str((CB/'receipt.json').absolute())],
            'parent_comparison_sha256':H(CA/'receipt.json'),
            'boundary':'Provisional source-directed rebase; source-current claim requires complete no-drift observations on this snapshot at both child runs and independent final comparison. The 848-project ancestor is author-only; external package-transitive and dynamic ancestry remain inherited.'}
OUT.mkdir()
with (OUT/'prepare.py').open('xb') as f: f.write(prep)
with (OUT/'replay.py').open('xb') as f: f.write(driver)
with (OUT/'manifest.json').open('x') as f: json.dump(manifest,f,indent=2,sort_keys=True);f.write('\n')
print('PROVISIONAL_INPUT',len(new['sources']),len(order),'manifest',H(OUT/'manifest.json'),
      'workspace_drift_before',len(before_drift),'workspace_drift_after',len(after_drift),flush=True)
