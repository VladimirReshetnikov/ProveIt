#!/usr/bin/env python3
"""Provisional design: rebuild eleven 14-variable modules; one axiom report."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time

D = Path(__file__).resolve().parent
M = D / 'manifest.json'
SNAP = D / 'sources'
PKG = Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL = LEAN.parent.parent / 'lib/lean'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.olean.hash',
            '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean', '.ilean.hash')
raw = M.read_bytes()
mh = hashlib.sha256(raw).hexdigest()
assert len(sys.argv) == 2 and sys.argv[1] == mh
m = json.loads(raw)
dh = H(__file__)
assert m['status'] == 'PROVISIONAL_14_AFTER_107_INPUT' and dh == m['driver_sha256']
P = Path(m['parent_state_path']).parent
R = Path(m['workspace_root'])
assert len(m['sources']) == 995 and len(m['workspace_sources']) == 1115 and len(m['order']) == 11
assert len(set(m['order'])) == 11 and m['order'][-1] == m['target']
dirty = set(m['order'])
excluded = {n.replace('.', '/') + s for n in dirty for s in SUFFIXES}

def inventory(root):
    out = {}
    for directory, _, names in os.walk(root / 'lib', followlinks=True):
        for name in names:
            if name.endswith(SUFFIXES):
                p = Path(directory) / name
                out[str(p.relative_to(root / 'lib'))] = {'sha256': H(p), 'resolved_path': str(p.resolve())}
    return out

def external():
    for name, row in m['external'].items():
        stem = name.replace('.', '/') + '.olean'
        pick = next((p for p in (PKG / stem, TOOL / stem) if p.is_file()), None)
        assert pick is not None and str(pick.resolve()) == row['selected']
        for path, rec in row['companions'].items():
            if rec is None:
                assert not os.path.lexists(path)
            else:
                assert Path(path).is_file() and str(Path(path).resolve()) == rec['realpath'] and H(path) == rec['sha256']
    for name in dirty:
        for root in (PKG, TOOL):
            for suffix in SUFFIXES:
                assert not os.path.lexists(root / (name.replace('.', '/') + suffix))
    for path, rec in m['parent_fallback_companions'].items():
        if rec is None:
            assert not os.path.lexists(path)
        else:
            assert Path(path).is_file() and str(Path(path).resolve()) == rec['realpath'] and H(path) == rec['sha256']
    assert set(m['parent_external_direct_paths']) == set(m['parent_external_resolved_paths'])
    for path, val in m['parent_external_direct_paths'].items():
        assert H(path) == val and str(Path(path).resolve()) == m['parent_external_resolved_paths'][path]
    assert all(not os.path.lexists(p) for p in m['parent_external_absent_paths'])

def frozen():
    assert H(M) == mh and H(__file__) == dh and H(D / 'prepare.py') == m['preparer_sha256']
    assert H(LEAN) == m['lean_sha256'] and H(P / 'state.json') == m['parent_state_sha256']
    assert all(str(Path(p).resolve()) == p and H(p) == v for p, v in m['gate_guard'].items())
    assert all(str(Path(p).resolve()) == p and H(p) == v for p, v in m['origin_guard'].items())
    for name, row in m['sources'].items():
        path = SNAP / (name.replace('.', '/') + '.lean')
        assert path.is_file() and not path.is_symlink() and path.resolve() == path.absolute() and H(path) == row['sha256']
    assert inventory(P) == m['parent_inventory']
    external()

seen = set()
for name in m['order']:
    actual = re.findall(r'^import\s+([A-Z][\w.]*)', (SNAP / (name.replace('.', '/') + '.lean')).read_text(), re.M)
    assert actual == m['sources'][name]['imports']
    assert all(n not in dirty or n in seen for n in actual)
    seen.add(name)
frozen()
work = Path(tempfile.mkdtemp(prefix='ipra14-current-followup-'))
lib = work / 'lib'
logs = work / 'logs'
lib.mkdir()
logs.mkdir()
(work / 'manifest.json').write_bytes(raw)
(work / 'driver.py').write_bytes(Path(__file__).read_bytes())
for rel, row in m['parent_inventory'].items():
    if rel not in excluded:
        dst = lib / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.symlink_to(row['resolved_path'])

def drift():
    out = []
    for name, row in m['workspace_sources'].items():
        p = R / row['path']
        try:
            actual = H(p) if p.is_file() else None
        except OSError:
            actual = None
        if actual != row['sha256']:
            out.append({'module': name, 'expected': row['sha256'], 'actual': actual})
    return out

state = {'status': 'RUNNING', 'manifest_sha256': mh, 'driver_sha256': dh,
         'parent_state_sha256': m['parent_state_sha256'], 'records': [],
         'workspace_drift_before': drift(), 'boundary': m['boundary']}
def save():
    (work / 'state.json').write_text(json.dumps(state, sort_keys=True, indent=2) + '\n')

def audit():
    frozen()
    assert H(work / 'manifest.json') == mh and H(work / 'driver.py') == dh
    expected = {k: v for k, v in m['parent_inventory'].items() if k not in excluded}
    for row in state['records']:
        if row['exit'] == 0:
            rel = row['name'].replace('.', '/') + '.olean'
            p = lib / rel
            assert p.is_file() and not p.is_symlink() and p.resolve() == p.absolute()
            expected[rel] = {'sha256': row['object_sha256'], 'resolved_path': str(p.absolute())}
            assert H(logs / (row['name'].replace('.', '_') + '.log')) == row['log_sha256']
            for dep, info in row['direct_imports'].items():
                q = Path(m['external'][dep]['selected']) if dep in m['external'] else lib / (dep.replace('.', '/') + '.olean')
                assert q.exists() and str(q.resolve()) == info['resolved_path'] and H(q) == info['sha256']
    assert inventory(work) == expected

def warnings(text):
    out = []
    tests = [('unused_simp', r'^This simp argument is unused:'),
             ('unused_section', r'^automatically included section variable\(s\) unused in theorem '),
             ('unused_variable', r'^Variable name `[^`]+` is not explicitly referenced\.$'),
             ('simp_suggestion', r"^(?:try 'simp' instead of 'simpa'|Try `simp at this` instead of `simpa using this`)$"),
             ('noop_tactic', r"^'.+' tactic does nothing$"), ('unreachable_tactic', r'^this tactic is never executed$'),
             ('deprecation', r'^`[^`]+` has been deprecated(?:[.:].*)?$'),
             ('simp_discrimination', r'^Left-hand side of simp theorem is headed by a `\.other` key in the discrimination tree'),
             ('tactic_sequence', r'^Used `tac1 <;> tac2` where `\(tac1; tac2\)` would suffice$'),
             ('exponent_threshold_notice', r'^exponent [0-9]+ exceeds the threshold [0-9]+, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold$')]
    for line in text.splitlines():
        if 'warning:' not in line:
            continue
        msg = line.split('warning:', 1)[1].strip()
        hits = [cat for cat, pat in tests if re.search(pat, msg)]
        assert len(hits) == 1, ('unrecognized warning', line)
        out.append({'category': hits[0], 'message': msg, 'full_line': line})
    return out

save()
print('PRIVATE', work, flush=True)
try:
    audit()
    env = dict(os.environ, LEAN_PATH=str(lib) + ':' + str(PKG), LEAN_NUM_THREADS='1')
    env.pop('LEAN_SRC_PATH', None)
    for name in m['order']:
        obj = lib / (name.replace('.', '/') + '.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        log = logs / (name.replace('.', '_') + '.log')
        direct = {}
        start = time.monotonic()
        for dep in m['sources'][name]['imports']:
            p = Path(m['external'][dep]['selected']) if dep in m['external'] else lib / (dep.replace('.', '/') + '.olean')
            assert p.exists(), str(p)
            direct[dep] = {'sha256': H(p), 'resolved_path': str(p.resolve())}
        with log.open('w') as out:
            proc = subprocess.run([str(LEAN), '-M8000', '-j1', '-DElab.async=false', '--root=' + str(SNAP),
                                   str(SNAP / (name.replace('.', '/') + '.lean')), '-o', str(obj)],
                                  cwd=R, env=env, stdout=out, stderr=subprocess.STDOUT)
        row = {'name': name, 'exit': proc.returncode, 'object_sha256': H(obj) if obj.exists() else None,
               'log_sha256': H(log), 'direct_imports': direct, 'seconds': time.monotonic() - start}
        state['records'].append(row)
        save()
        print(name, proc.returncode, flush=True)
        text = log.read_text()
        assert proc.returncode == 0 and 'error:' not in text and 'sorryAx' not in text and not re.search(r'\b(?:sorry|admit)\b', text)
        row['warnings'] = warnings(text)
        save()
        if name == m['target']:
            reports = re.findall(r'depends on axioms: \[([^\]]*)\]', text)
            assert len(reports) == 1 and set(x.strip() for x in reports[0].split(',')) == {'propext', 'Classical.choice', 'Quot.sound'}
    audit()
    state['workspace_drift_after'] = drift()
    state['source_matches_workspace_at_final_check'] = not state['workspace_drift_after']
    state['status'] = 'PASS'
    save()
    print('PASS', work, flush=True)
except BaseException as exc:
    state.update(status='FAILED', failure=repr(exc))
    save()
    raise
