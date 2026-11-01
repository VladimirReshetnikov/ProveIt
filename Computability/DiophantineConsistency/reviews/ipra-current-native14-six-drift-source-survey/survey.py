#!/usr/bin/env python3
"""Freeze a 14-variable source candidate atop the six-edit 13-source snapshot."""
import hashlib
import json
from pathlib import Path
import subprocess

D = Path(__file__).resolve().parent
V = D.parent
R = D.parents[3]
BASE = V / 'ipra-current-repaired-six-drift-source-survey'
OLD = V / 'ipra-current-native14-source-survey-v2'
EXTRA = V / 'ipra-current-native14-frozen-extra' / 'sources'
H = lambda b: hashlib.sha256(b).hexdigest()
inputs = [Path(__file__).resolve(), BASE / 'manifest.json', BASE / 'lean-deps-receipt.json',
          OLD / 'manifest.json', OLD / 'lean-deps-receipt.json']
before = {str(p): H(p.read_bytes()) for p in inputs}
head_before = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
base = json.loads((BASE / 'manifest.json').read_text())
old = json.loads((OLD / 'manifest.json').read_text())
assert base['status'] == 'CANDIDATE_SOURCE_SNAPSHOT'
assert old['status'] == 'PROSPECTIVE_SOURCE_GRAPH'
shared = set(base['sources']) & set(old['sources'])
extra = set(old['sources']) - set(base['sources'])
assert len(old['sources']) == 995 and len(shared) == 984 and len(extra) == 11
assert set(old['extra_order']) == extra and old['extra_order'][-1] == old['target']
records = {}
for name, row in old['sources'].items():
    if name in shared:
        new = base['sources'][name]
        assert new['path'] == row['path'] and new['imports'] == row['imports'], name
        records[name] = new
    else:
        records[name] = row
def drift():
    out = []
    for name, row in records.items():
        path = R / row['path']
        try:
            digest = H(path.read_bytes()) if path.is_file() else None
        except OSError:
            digest = None
        if digest != row['sha256']:
            out.append({'module': name, 'expected': row['sha256'], 'actual': digest})
    return out
initial = drift()
assert not initial, ('workspace moved before source capture', initial)
snap = D / 'sources'
snap.mkdir()
for name, row in records.items():
    root = (BASE / 'sources') if name in shared else EXTRA
    src = root / (name.replace('.', '/') + '.lean')
    assert src.is_file() and not src.is_symlink() and H(src.read_bytes()) == row['sha256'], name
    raw = src.read_bytes()
    assert H(raw) == row['sha256'], name
    dest = snap / (name.replace('.', '/') + '.lean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    with dest.open('xb') as f:
        f.write(raw)
    assert dest.is_file() and not dest.is_symlink() and H(dest.read_bytes()) == row['sha256']
assert {str(p): H(p.read_bytes()) for p in inputs} == before
assert all(H((snap / (n.replace('.', '/') + '.lean')).read_bytes()) == row['sha256'] for n,row in records.items())
final = drift()
head_after = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
out = {'status': 'CANDIDATE_SOURCE_SNAPSHOT', 'input_sha256': before,
       'sources': records, 'extra_order': old['extra_order'], 'target': old['target'],
       'external': old['external'], 'workspace_drift_before': initial, 'workspace_drift_after': final,
       'head_before': head_before, 'head_after': head_after,
       'boundary': 'Source candidate only; the matched 107 parent, retained object environments, '
                   'external companions and a guarded 14-variable successor/replay require separate authentication.'}
manifest = D / 'manifest.json'
with manifest.open('x') as f:
    json.dump(out, f, indent=2, sort_keys=True)
    f.write('\n')
print('CANDIDATE_SOURCE_SNAPSHOT', len(records), len(shared), len(extra), 'final_drift', len(final), H(manifest.read_bytes()))
