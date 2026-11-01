#!/usr/bin/env python3
"""Provisional design: freeze the 11-module successor only after parent gates."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys

if len(sys.argv) != 6:
    raise SystemExit('usage: prepare.py OUTPUT COMPARISON_DIR AUTHOR_EXIT PEER_EXIT WRAPPER_EXIT')
OUT, COMP, AE, BE, WE = (Path(x).absolute() for x in sys.argv[1:])
R = Path.cwd().resolve()
V = R / 'Computability/DiophantineConsistency/reviews'
S13 = V / 'ipra-current-repaired-survey'
S14 = V / 'ipra-current-native14-source-survey-v2'
EXTRA = V / 'ipra-current-native14-frozen-extra/sources'
PKG = Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL = LEAN.parent.parent / 'lib/lean'
REPLAY = Path(__file__).resolve().parent / 'replay.py'
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.olean.hash',
            '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean', '.ilean.hash')
sha = lambda b: hashlib.sha256(b).hexdigest()
h = lambda p: sha(Path(p).read_bytes())
gate = {}
def pin(path, expected=None):
    p = Path(path).absolute()
    assert p.is_file() and p.resolve() == p, ('noncanonical gate', str(p))
    val = h(p)
    assert expected is None or val == expected, (str(p), val, expected)
    assert str(p) not in gate or gate[str(p)] == val
    gate[str(p)] = val
    return val
def load(path):
    pin(path)
    return json.loads(Path(path).read_text())
def inventory(root):
    out = {}
    for directory, _, names in os.walk(root / 'lib', followlinks=True):
        for name in names:
            if name.endswith(SUFFIXES):
                p = Path(directory) / name
                out[str(p.relative_to(root / 'lib'))] = {'sha256': h(p), 'resolved_path': str(p.resolve())}
    return out
def observation(path, state_path, state_hash):
    o = load(path)
    assert o['status'] == 'PASS_EXIT_0' and o['exit_code'] == 0
    assert o['evidence_kind'] == 'tool_session_observation' and o['session_id']
    assert o['state_path'] == str(state_path) and o['state_sha256'] == state_hash
    return o
def audit_ext(s13, parent):
    assert set(parent['parent_external_direct_paths']) == set(parent['parent_external_resolved_paths'])
    for path, value in parent['parent_external_direct_paths'].items():
        assert h(path) == value and str(Path(path).resolve()) == parent['parent_external_resolved_paths'][path]
    assert all(not os.path.lexists(p) for p in parent['parent_external_absent_paths'])
    for name, row in s13['external'].items():
        stem = name.replace('.', '/') + '.olean'
        selected = next((p for p in (PKG / stem, TOOL / stem) if p.is_file()), None)
        assert selected is not None and str(selected.resolve()) == row['selected']
        for path, item in row['companions'].items():
            if item is None:
                assert not os.path.lexists(path)
            else:
                assert Path(path).is_file() and str(Path(path).resolve()) == item['realpath'] and h(path) == item['sha256']

assert not OUT.exists(), 'refusing to overwrite'
prep = Path(__file__).read_bytes()
driver = REPLAY.read_bytes()
comparator = load(COMP / 'receipt.json')
terminal = load(COMP / 'terminal.json')
assert comparator['status'] == 'MATCHED_PASS' and comparator['rows'] == 258
assert terminal['status'] == 'PASS_COMPARATOR_EXIT_0' and terminal['comparator_exit_code'] == 0
assert terminal['before'] == terminal['after'] and terminal['receipt_sha256'] == h(COMP / 'receipt.json')
pin(COMP / 'compare.py', comparator['compare_sha256'])
pin(COMP / 'run.py', terminal['before'][str((COMP / 'run.py').resolve())])
pin(COMP / 'run.log', terminal['log_sha256'])
for path, value in terminal['before'].items():
    pin(path, value)
assert (COMP / 'run.log').read_text() == (f"MATCHED_PASS 258 rows {comparator['guarded_file_count']} files "
                                           f"workspace_matches {comparator['workspace_matches_snapshot_through_observations']}\n")
A, B = Path(comparator['author_path']), Path(comparator['peer_path'])
assert A.resolve() != B.resolve() and not os.path.samefile(A / 'state.json', B / 'state.json')
a, b = load(A / 'state.json'), load(B / 'state.json')
ah, bh = h(A / 'state.json'), h(B / 'state.json')
assert ah == comparator['author_state_sha256'] and bh == comparator['peer_state_sha256']
assert a['status'] == b['status'] == 'PASS' and len(a['records']) == len(b['records']) == 258
observation(AE, A / 'state.json', ah)
observation(BE, B / 'state.json', bh)
wrapper = load(WE)
assert wrapper['status'] == 'PASS_EXIT_0' and wrapper['exit_code'] == 0
assert wrapper['evidence_kind'] == 'tool_session_observation' and wrapper['session_id']
assert wrapper['terminal_path'] == str(COMP / 'terminal.json') and wrapper['terminal_sha256'] == h(COMP / 'terminal.json')

# The comparator records the plan hash, but not its path. It must be supplied in
# the durable wrapper input map; the unique matching pinned manifest is selected.
plan_candidates = [Path(p) for p, val in terminal['before'].items()
                   if Path(p).name == 'manifest.json' and val == comparator['manifest_sha256']]
assert len(plan_candidates) == 1, ('parent plan is not uniquely identified', plan_candidates)
M258 = plan_candidates[0]
m258 = load(M258)
assert h(M258.parent / 'replay.py') == m258['driver_sha256'] == comparator['driver_sha256']
pin(M258.parent / 'replay.py', m258['driver_sha256'])
assert a['manifest_sha256'] == b['manifest_sha256'] == comparator['manifest_sha256']
assert a['driver_sha256'] == b['driver_sha256'] == comparator['driver_sha256']
s13 = load(S13 / 'manifest.json')
s14 = load(S14 / 'manifest.json')
deps = load(S14 / 'lean-deps-receipt.json')
assert h(S13 / 'manifest.json') == m258['survey_manifest_sha256'] == comparator['survey_manifest_sha256']
assert s14['status'] == 'PROSPECTIVE_SOURCE_GRAPH' and len(s14['sources']) == 995
assert len(s14['extra_order']) == len(set(s14['extra_order'])) == 11 and s14['extra_order'][-1] == s14['target']
assert deps['status'] == 'PASS_HEADER_DEPS' and set(deps['rows']) == set(s14['extra_order'])
for path, value in {**s14['input_sha256'], **deps['input_sha256']}.items():
    pin(path, value)
assert deps['input_sha256'][str((S14 / 'manifest.json').absolute())] == h(S14 / 'manifest.json')
assert set(s14['external']) <= set(s13['external']) and h(LEAN) == m258['lean_sha256']
# Preserve the complete source environment behind all 258 parent outputs,
# including parent sources that are outside the smaller 14-target closure.
assert len(s13['sources']) == 1099
for name, row in s13['sources'].items():
    pin(S13 / 'sources' / (name.replace('.', '/') + '.lean'), row['sha256'])
for path, value in m258['gate_guard'].items():
    pin(path, value)
assert all(str(Path(p).resolve()) == p and h(p) == v for p, v in m258['origin_guard'].items())
assert all(h(p) == v for p, v in gate.items())

old_dirty = set(s13['order'])
old_excluded = {n.replace('.', '/') + suf for n in old_dirty for suf in SUFFIXES}
expected = {k: v for k, v in m258['parent_inventory'].items() if k not in old_excluded}
assert [r['name'] for r in a['records']] == [r['name'] for r in b['records']] == s13['order']
for x, y in zip(a['records'], b['records']):
    assert all(x.get(k) == y.get(k) for k in ('name', 'exit', 'object_sha256', 'log_sha256', 'warnings')) and x['exit'] == 0
    assert {n: v['sha256'] for n, v in x['direct_imports'].items()} == {n: v['sha256'] for n, v in y['direct_imports'].items()}
    for root, row in ((A, x), (B, y)):
        obj = root / 'lib' / (row['name'].replace('.', '/') + '.olean')
        assert obj.is_file() and not obj.is_symlink() and obj.resolve() == obj.absolute()
        pin(obj, row['object_sha256'])
        pin(root / 'logs' / (row['name'].replace('.', '_') + '.log'), row['log_sha256'])
        for info in row['direct_imports'].values():
            pin(info['resolved_path'], info['sha256'])
    rel = x['name'].replace('.', '/') + '.olean'
    expected[rel] = {'sha256': y['object_sha256'], 'resolved_path': str((B / 'lib' / rel).absolute())}
assert inventory(B) == expected

extra = set(s14['extra_order'])
assert extra == set(s14['sources']) - set(s13['sources'])
assert len(set(s14['sources']) & set(s13['sources'])) == 984
for name, rec in s14['sources'].items():
    src = (EXTRA if name in extra else S13 / 'sources') / (name.replace('.', '/') + '.lean')
    assert src.is_file() and not src.is_symlink() and src.resolve() == src.absolute() and h(src) == rec['sha256']
    if name not in extra:
        assert rec['sha256'] == s13['sources'][name]['sha256']
for name in extra:
    for root in (PKG, TOOL):
        for suffix in SUFFIXES:
            assert not os.path.lexists(root / (name.replace('.', '/') + suffix))
audit_ext(s13, m258)
assert all(str(Path(p).resolve()) == p and h(p) == v for p, v in m258['origin_guard'].items())
assert all(h(p) == v for p, v in gate.items())
assert inventory(B) == expected and h(REPLAY) == sha(driver) and h(__file__) == sha(prep)

# Publication is deliberately exclusive. Source snapshots are copies, not links.
OUT.mkdir()
snap = OUT / 'sources'
for name, rec in s14['sources'].items():
    src = (EXTRA if name in extra else S13 / 'sources') / (name.replace('.', '/') + '.lean')
    dst = snap / (name.replace('.', '/') + '.lean')
    dst.parent.mkdir(parents=True, exist_ok=True)
    with dst.open('xb') as out:
        out.write(src.read_bytes())
    assert dst.is_file() and not dst.is_symlink() and h(dst) == rec['sha256']
# A failed post-copy audit leaves a partial directory without a success manifest.
assert all(h((EXTRA if n in extra else S13 / 'sources') / (n.replace('.', '/') + '.lean')) == row['sha256']
           for n, row in s14['sources'].items())
assert all(str(Path(p).resolve()) == p and h(p) == v for p, v in gate.items())
assert all(str(Path(p).resolve()) == p and h(p) == v for p, v in m258['origin_guard'].items())
assert inventory(B) == expected
audit_ext(s13, m258)
for name in extra:
    for root in (PKG, TOOL):
        for suffix in SUFFIXES:
            assert not os.path.lexists(root / (name.replace('.', '/') + suffix))
assert h(REPLAY) == sha(driver) and h(__file__) == sha(prep)
manifest = {'status': 'PROVISIONAL_DESIGN_INPUT', 'workspace_root': str(R), 'parent_state_path': str(B / 'state.json'),
            'parent_comparison_receipt_path': str((COMP / 'receipt.json').absolute()),
            'parent_comparison_receipt_sha256': h(COMP / 'receipt.json'),
            'parent_state_sha256': bh, 'parent_inventory': expected, 'gate_guard': gate,
            'origin_guard': m258['origin_guard'], 'external': s13['external'],
            'parent_external_direct_paths': m258['parent_external_direct_paths'],
            'parent_external_resolved_paths': m258['parent_external_resolved_paths'],
            'parent_external_absent_paths': m258['parent_external_absent_paths'],
            'sources': s14['sources'], 'workspace_sources': s13['sources'] | {n: s14['sources'][n] for n in extra},
            'order': s14['extra_order'], 'target': s14['target'], 'lean_sha256': m258['lean_sha256'],
            'driver_sha256': sha(driver), 'preparer_sha256': sha(prep),
            'boundary': 'Provisional design only. Source-current status requires the parent comparator workspace_matches_snapshot_through_observations, both child replays matching all 1110 workspace source paths before and after, and a fresh final child comparator scan with no drift. These are point-in-time observations. 848 ancestor author-only; package-transitive and dynamic ancestry inherited.'}
with (OUT / 'prepare.py').open('xb') as out: out.write(prep)
with (OUT / 'replay.py').open('xb') as out: out.write(driver)
with (OUT / 'manifest.json').open('x') as out: json.dump(manifest, out, sort_keys=True, indent=2); out.write('\n')
print('PROVISIONAL_INPUT', len(s14['sources']), len(extra), h(OUT / 'manifest.json'))
