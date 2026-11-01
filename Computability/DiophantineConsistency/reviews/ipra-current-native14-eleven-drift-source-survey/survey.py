#!/usr/bin/env python3
"""Capture the 14-variable source candidate after three later proof edits."""
import hashlib
import json
from pathlib import Path
import subprocess

D = Path(__file__).resolve().parent
V = D.parent
R = D.parents[3]
BASE = V / 'ipra-current-repaired-eleven-drift-source-survey'
OLD = V / 'ipra-current-native14-eight-drift-source-survey'
H = lambda b: hashlib.sha256(b).hexdigest()
inputs = [Path(__file__).resolve(), BASE / 'manifest.json', BASE / 'lean-deps-receipt.json',
          OLD / 'manifest.json', OLD / 'dependency-inheritance-receipt.json']
before = {str(p): H(p.read_bytes()) for p in inputs}
head_before = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
base, old = (json.loads((p / 'manifest.json').read_text()) for p in (BASE, OLD))
assert base['status'] == old['status'] == 'CANDIDATE_SOURCE_SNAPSHOT'
shared = set(base['sources']) & set(old['sources'])
extra = set(old['sources']) - set(base['sources'])
assert len(old['sources']) == 995 and len(shared) == 984 and len(extra) == 11
assert set(old['extra_order']) == extra and old['extra_order'][-1] == old['target']
seeds = {'DiophantineConsistency.PRAWitnessCalculus',
         'DiophantineConsistency.PRAWitnessFormulaFunctions', 'ZFCinPA.SetCongruence'}
assert seeds <= shared and seeds <= set(base['seeds'])
records = {}
for n,row in old['sources'].items():
    if n in shared:
        new = base['sources'][n]
        assert new['path'] == row['path'], n
        if n in seeds:
            assert new['imports'] == row['imports'] and new['sha256'] != row['sha256']
        else:
            assert new == row, n
        records[n] = new
    else:
        records[n] = row
reachable = set()
queue = [old['target']]
while queue:
    n = queue.pop()
    if n in reachable:
        continue
    reachable.add(n)
    queue.extend(x for x in records[n]['imports'] if x in records)
assert reachable == set(records), ('changed graph reachability', len(reachable), len(records))
def drift():
    out = []
    for n,row in records.items():
        path = R / row['path']
        try: digest = H(path.read_bytes()) if path.is_file() else None
        except OSError: digest = None
        if digest != row['sha256']:
            out.append({'module': n, 'expected': row['sha256'], 'actual': digest})
    return out
initial = drift()
assert not initial, ('workspace moved before source capture', initial)
snap = D / 'sources'
snap.mkdir()
for n,row in records.items():
    root = (BASE / 'sources') if n in shared else (OLD / 'sources')
    src = root / (n.replace('.', '/') + '.lean')
    assert src.is_file() and not src.is_symlink() and H(src.read_bytes()) == row['sha256'], n
    raw = src.read_bytes()
    assert H(raw) == row['sha256']
    dst = snap / (n.replace('.', '/') + '.lean')
    dst.parent.mkdir(parents=True, exist_ok=True)
    with dst.open('xb') as f: f.write(raw)
    assert dst.is_file() and not dst.is_symlink() and H(dst.read_bytes()) == row['sha256']
assert {str(p): H(p.read_bytes()) for p in inputs} == before
assert all(H((snap / (n.replace('.', '/') + '.lean')).read_bytes()) == row['sha256'] for n,row in records.items())
final = drift()
head_after = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
out = {'status': 'CANDIDATE_SOURCE_SNAPSHOT', 'input_sha256': before, 'sources': records,
       'extra_order': old['extra_order'], 'target': old['target'], 'external': old['external'],
       'workspace_drift_before': initial, 'workspace_drift_after': final,
       'head_before': head_before, 'head_after': head_after,
       'boundary': 'Source candidate only; a matched seventh-drift parent, retained object origins, '
                   'external companions and a guarded 14-variable successor require separate authentication.'}
manifest = D / 'manifest.json'
with manifest.open('x') as f: json.dump(out, f, indent=2, sort_keys=True); f.write('\n')
print('CANDIDATE_SOURCE_SNAPSHOT', len(records), len(shared), len(extra), 'final_drift', len(final), H(manifest.read_bytes()))
