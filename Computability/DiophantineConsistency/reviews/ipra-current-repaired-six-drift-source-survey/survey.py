#!/usr/bin/env python3
"""Freeze a six-edit source candidate; this is not an object/replay audit."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

D = Path(__file__).resolve().parent
V = D.parent
R = D.parents[3]
BASE = V / 'ipra-current-repaired-survey'
PRE = V / 'ipra-current-repaired-postmerge-preliminary-v3' / 'manifest.json'
H = lambda b: hashlib.sha256(b).hexdigest()
files = [Path(__file__).resolve(), BASE / 'manifest.json', PRE]
before = {str(p): H(p.read_bytes()) for p in files}
head_before = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
base = json.loads((BASE / 'manifest.json').read_text())
pre = json.loads(PRE.read_text())
assert pre['status'] == 'PRELIMINARY_SOURCE_REVERSE_CLOSURE'
assert pre['input_sha256'][str(BASE / 'manifest.json')] == before[str(BASE / 'manifest.json')]
assert len(base['sources']) == 1099 and len(pre['drift']) == 6
assert len(pre['impacted']) == len(pre['source_topological_order']) == 107
assert set(pre['impacted']) == set(pre['source_topological_order'])
records = {}
for name, row in base['sources'].items():
    captured = BASE / 'sources' / (name.replace('.', '/') + '.lean')
    assert captured.is_file() and not captured.is_symlink() and H(captured.read_bytes()) == row['sha256']
    expected = pre['drift'].get(name, {}).get('workspace', row['sha256'])
    records[name] = {'path': row['path'], 'sha256': expected, 'imports': row['imports']}
def drift():
    result = []
    for name, row in records.items():
        path = R / row['path']
        try:
            val = H(path.read_bytes()) if path.is_file() else None
        except OSError:
            val = None
        if val != row['sha256']:
            result.append({'module': name, 'expected': row['sha256'], 'actual': val})
    return result
initial = drift()
assert not initial, ('workspace moved before source capture', initial)
snap = D / 'sources'
snap.mkdir()
for name, row in records.items():
    src = (R / row['path']) if name in pre['drift'] else (BASE / 'sources' / (name.replace('.', '/') + '.lean'))
    raw = src.read_bytes()
    assert H(raw) == row['sha256'], name
    if name in pre['drift']:
        assert re.findall(r'^import\s+([A-Z][\w.]*)', raw.decode('utf-8'), re.M) == row['imports']
    dest = snap / (name.replace('.', '/') + '.lean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    with dest.open('xb') as out:
        out.write(raw)
    assert dest.is_file() and not dest.is_symlink() and H(dest.read_bytes()) == row['sha256']
assert {str(p): H(p.read_bytes()) for p in files} == before
assert all(H((snap / (n.replace('.', '/') + '.lean')).read_bytes()) == row['sha256'] for n, row in records.items())
final = drift()
head_after = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
out = {'status': 'CANDIDATE_SOURCE_SNAPSHOT', 'input_sha256': before,
       'sources': records, 'order': pre['source_topological_order'], 'target': base['target'],
       'external': base['external'], 'workspace_drift_before': initial, 'workspace_drift_after': final,
       'head_before': head_before, 'head_after': head_after,
       'boundary': 'Source candidate only; original retained-object environments, completed 258 parent, '
                   'Lean dependency parsing, external companions and final successor closure/replay require separate authentication.'}
manifest = D / 'manifest.json'
with manifest.open('x') as f:
    json.dump(out, f, indent=2, sort_keys=True)
    f.write('\n')
print('CANDIDATE_SOURCE_SNAPSHOT', len(records), len(out['order']), 'final_drift', len(final), H(manifest.read_bytes()))
