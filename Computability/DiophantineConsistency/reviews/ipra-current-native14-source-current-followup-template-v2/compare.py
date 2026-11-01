#!/usr/bin/env python3
"""Provisional comparison of the source-directed 11-module 14-variable replay."""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import sys

if len(sys.argv) != 5:
    raise SystemExit('usage: compare.py PLAN AUTHOR PEER PARENT_COMPARATOR_RECEIPT')
PLAN, A, B, PARENT_RECEIPT = (Path(x).absolute() for x in sys.argv[1:])
D = Path(__file__).resolve().parent
PKG = Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL = LEAN.parent.parent / 'lib/lean'
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.olean.hash',
            '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean', '.ilean.hash')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
    raw = Path(p).read_bytes()
    return json.loads(raw), hashlib.sha256(raw).hexdigest()

assert A.resolve() != B.resolve() and not os.path.samefile(A / 'state.json', B / 'state.json'), \
       'author and peer must be independent runs'
M, DR, SNAP = PLAN / 'manifest.json', PLAN / 'replay.py', PLAN / 'sources'
m, mh = read(M)
a, ah = read(A / 'state.json')
b, bh = read(B / 'state.json')
parent_comparison, ph = read(PARENT_RECEIPT)
P = Path(m['parent_state_path']).parent
R = Path(m['workspace_root'])
dh, ch = H(DR), H(__file__)
assert m['status'] == 'PROVISIONAL_DESIGN_INPUT'
assert len(m['sources']) == 995 and len(m['workspace_sources']) == 1110
assert len(m['order']) == len(set(m['order'])) == 11 and m['order'][-1] == m['target']
assert a['status'] == b['status'] == 'PASS'
assert a['manifest_sha256'] == b['manifest_sha256'] == mh
assert a['driver_sha256'] == b['driver_sha256'] == dh == m['driver_sha256']
assert a['parent_state_sha256'] == b['parent_state_sha256'] == m['parent_state_sha256']
for state in (a, b):
    for key in ('workspace_drift_before', 'workspace_drift_after'):
        assert isinstance(state[key], list)
    assert state['source_matches_workspace_at_final_check'] == (not state['workspace_drift_after'])
assert [r['name'] for r in a['records']] == [r['name'] for r in b['records']] == m['order']
assert str(PARENT_RECEIPT.resolve()) == str(PARENT_RECEIPT)
assert m['parent_comparison_receipt_path'] == str(PARENT_RECEIPT)
assert m['parent_comparison_receipt_sha256'] == ph
assert m['gate_guard'][str(PARENT_RECEIPT)] == ph
assert parent_comparison['status'] == 'MATCHED_PASS' and parent_comparison['rows'] == 258
assert Path(parent_comparison['peer_path']).resolve() == P.resolve()
assert parent_comparison['peer_state_sha256'] == m['parent_state_sha256']
assert isinstance(parent_comparison['workspace_matches_snapshot_through_observations'], bool)

files = {}
def add(p, value):
    key = str(Path(p))
    assert key not in files or files[key] == value, (key, files[key], value)
    files[key] = value

for p, v in m['gate_guard'].items():
    assert str(Path(p).resolve()) == p
    add(p, v)
for p, v in m['origin_guard'].items():
    assert str(Path(p).resolve()) == p
    add(p, v)
for p, v in m['parent_external_direct_paths'].items():
    add(p, v)
add(LEAN, m['lean_sha256'])
add(P / 'state.json', m['parent_state_sha256'])
add(PLAN / 'prepare.py', m['preparer_sha256'])
for root in (A, B):
    add(root / 'driver.py', dh)
    add(root / 'manifest.json', mh)
for name, row in m['sources'].items():
    path = SNAP / (name.replace('.', '/') + '.lean')
    assert path.is_file() and not path.is_symlink() and path.resolve() == path.absolute()
    add(path, row['sha256'])
for rel, row in m['parent_inventory'].items():
    assert str((P / 'lib' / rel).resolve()) == row['resolved_path']
    add(P / 'lib' / rel, row['sha256'])
for row in m['external'].values():
    for path, item in row['companions'].items():
        if item is not None:
            add(path, item['sha256'])

def warnings(text):
    out = []
    tests = [('unused_simp', r'^This simp argument is unused:'),
             ('unused_section', r'^automatically included section variable\(s\) unused in theorem '),
             ('unused_variable', r'^Variable name `[^`]+` is not explicitly referenced\.$'),
             ('simp_suggestion', r"^(?:try 'simp' instead of 'simpa'|Try `simp at this` instead of `simpa using this`)$"),
             ('noop_tactic', r"^'.+' tactic does nothing$"),
             ('unreachable_tactic', r'^this tactic is never executed$'),
             ('deprecation', r'^`[^`]+` has been deprecated(?:[.:].*)?$'),
             ('simp_discrimination', r'^Left-hand side of simp theorem is headed by a `\.other` key in the discrimination tree'),
             ('tactic_sequence', r'^Used `tac1 <;> tac2` where `\(tac1; tac2\)` would suffice$'),
             ('exponent_threshold_notice', r'^exponent [0-9]+ exceeds the threshold [0-9]+, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold$')]
    for line in text.splitlines():
        if 'warning:' not in line:
            continue
        msg = line.split('warning:', 1)[1].strip()
        hits = [category for category, pattern in tests if re.search(pattern, msg)]
        assert len(hits) == 1, ('unrecognized warning', line)
        out.append({'category': hits[0], 'message': msg, 'full_line': line})
    return out

dirty = set(m['order'])
seen = set()
for name in m['order']:
    src = SNAP / (name.replace('.', '/') + '.lean')
    actual = re.findall(r'^import\s+([A-Z][\w.]*)', src.read_text(), re.M)
    assert actual == m['sources'][name]['imports']
    assert all(dep not in dirty or dep in seen for dep in actual)
    seen.add(name)
for x, y in zip(a['records'], b['records']):
    assert all(x.get(k) == y.get(k) for k in ('name', 'exit', 'object_sha256', 'log_sha256', 'warnings'))
    assert x['exit'] == y['exit'] == 0
    assert {n: v['sha256'] for n, v in x['direct_imports'].items()} == \
           {n: v['sha256'] for n, v in y['direct_imports'].items()}
    for root, row in ((A, x), (B, y)):
        name = row['name']
        assert set(row['direct_imports']) == set(m['sources'][name]['imports'])
        add(root / 'lib' / (name.replace('.', '/') + '.olean'), row['object_sha256'])
        log = root / 'logs' / (name.replace('.', '_') + '.log')
        add(log, row['log_sha256'])
        text = log.read_text()
        assert 'error:' not in text and 'sorryAx' not in text and not re.search(r'\b(?:sorry|admit)\b', text)
        assert warnings(text) == row['warnings']
        if name == m['target']:
            reports = re.findall(r'depends on axioms: \[([^\]]*)\]', text)
            assert len(reports) == 1 and set(q.strip() for q in reports[0].split(',')) == \
                   {'propext', 'Classical.choice', 'Quot.sound'}
        for dep, info in row['direct_imports'].items():
            path = Path(m['external'][dep]['selected']) if dep in m['external'] else root / 'lib' / (dep.replace('.', '/') + '.olean')
            assert path.exists() and str(path.resolve()) == info['resolved_path'] and H(path) == info['sha256']
            add(info['resolved_path'], info['sha256'])

excluded = {name.replace('.', '/') + suffix for name in dirty for suffix in SUFFIXES}
def expected(root, state):
    out = {rel: row for rel, row in m['parent_inventory'].items() if rel not in excluded}
    for row in state['records']:
        rel = row['name'].replace('.', '/') + '.olean'
        path = root / 'lib' / rel
        assert path.is_file() and not path.is_symlink() and path.resolve() == path.absolute()
        out[rel] = {'sha256': row['object_sha256'], 'resolved_path': str(path.absolute())}
    return out

def inventory(root):
    out = {}
    for directory, _, names in os.walk(root / 'lib', followlinks=True):
        for name in names:
            if name.endswith(SUFFIXES):
                path = Path(directory) / name
                out[str(path.relative_to(root / 'lib'))] = {'sha256': H(path), 'resolved_path': str(path.resolve())}
    return out

expa, expb = expected(A, a), expected(B, b)
def external():
    assert set(m['parent_external_direct_paths']) == set(m['parent_external_resolved_paths'])
    assert all(str(Path(p).resolve()) == v for p, v in m['parent_external_resolved_paths'].items())
    assert all(not os.path.lexists(p) for p in m['parent_external_absent_paths'])
    for name, row in m['external'].items():
        stem = name.replace('.', '/') + '.olean'
        pick = next((p for p in (PKG / stem, TOOL / stem) if p.is_file()), None)
        assert pick is not None and str(pick.resolve()) == row['selected']
        for path, item in row['companions'].items():
            if item is None:
                assert not os.path.lexists(path)
            else:
                assert Path(path).is_file() and str(Path(path).resolve()) == item['realpath'] and H(path) == item['sha256']
    for name in dirty:
        for root in (PKG, TOOL):
            for suffix in SUFFIXES:
                assert not os.path.lexists(root / (name.replace('.', '/') + suffix))

def audit():
    assert H(M) == mh and H(DR) == dh and H(__file__) == ch
    assert H(A / 'state.json') == ah and H(B / 'state.json') == bh and H(PARENT_RECEIPT) == ph
    assert all(H(path) == value for path, value in files.items())
    assert all(str(Path(p).resolve()) == p for p in m['gate_guard'])
    assert all(str(Path(p).resolve()) == p for p in m['origin_guard'])
    assert all((p := SNAP / (n.replace('.', '/') + '.lean')).is_file() and not p.is_symlink() and p.resolve() == p.absolute() for n in m['sources'])
    assert all(str((P / 'lib' / rel).resolve()) == row['resolved_path'] for rel, row in m['parent_inventory'].items())
    external()
    assert inventory(A) == expa and inventory(B) == expb
    for root, state in ((A, a), (B, b)):
        for row in state['records']:
            for dep, info in row['direct_imports'].items():
                path = Path(m['external'][dep]['selected']) if dep in m['external'] else root / 'lib' / (dep.replace('.', '/') + '.olean')
                assert path.exists() and str(path.resolve()) == info['resolved_path'] and H(path) == info['sha256']

def workspace_drift():
    out = []
    for name, row in m['workspace_sources'].items():
        path = R / row['path']
        try:
            actual = H(path) if path.is_file() else None
        except OSError:
            actual = None
        if actual != row['sha256']:
            out.append({'module': name, 'expected': row['sha256'], 'actual': actual})
    return out

audit()
for reserved in ('receipt.json', 'author-state.json', 'independent-state.json', 'author-logs', 'independent-logs'):
    assert not (D / reserved).exists(), ('refusing to overwrite comparison evidence', reserved)
for root, label, state_sha in ((A, 'author', ah), (B, 'independent', bh)):
    dest = D / (label + '-logs')
    dest.mkdir()
    shutil.copyfile(root / 'state.json', D / (label + '-state.json'))
    assert H(D / (label + '-state.json')) == state_sha
    for row in a['records']:
        name = row['name'].replace('.', '_') + '.log'
        shutil.copyfile(root / 'logs' / name, dest / name)
        assert H(dest / name) == row['log_sha256']
audit()
now = workspace_drift()
audit()
now_confirm = workspace_drift()
parent_current = parent_comparison['workspace_matches_snapshot_through_observations']
current = parent_current and not now and not now_confirm and all(not state[k] for state in (a, b)
                                            for k in ('workspace_drift_before', 'workspace_drift_after'))
result = {'status': 'MATCHED_PASS', 'author_path': str(A), 'peer_path': str(B),
          'author_state_sha256': ah, 'peer_state_sha256': bh, 'manifest_sha256': mh,
          'driver_sha256': dh, 'compare_sha256': ch, 'rows': len(a['records']),
          'parent_comparator_receipt': str(PARENT_RECEIPT), 'parent_comparator_sha256': ph,
          'matched_rows': [{'name': row['name'], 'object_sha256': row['object_sha256'],
                            'log_sha256': row['log_sha256'], 'warnings': row['warnings']} for row in a['records']],
          'guarded_file_count': len(files),
          'workspace_drift': {'parent_comparator_match': parent_current,
                              'author_before': a['workspace_drift_before'], 'author_after': a['workspace_drift_after'],
                              'peer_before': b['workspace_drift_before'], 'peer_after': b['workspace_drift_after'],
                              'comparison_final': now, 'comparison_final_confirm': now_confirm},
          'workspace_matches_snapshot_through_observations': current, 'boundary': m['boundary']}
with (D / 'receipt.json').open('x') as out:
    json.dump(result, out, sort_keys=True, indent=2)
    out.write('\n')
print('MATCHED_PASS', len(a['records']), 'rows', len(files), 'files', 'workspace_matches', current)
