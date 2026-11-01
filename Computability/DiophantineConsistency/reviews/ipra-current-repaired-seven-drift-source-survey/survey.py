#!/usr/bin/env python3
"""Capture the SeparationKernel source change; not an authenticated rebase."""
import collections
import graphlib
import hashlib
import json
from pathlib import Path
import re
import subprocess

D = Path(__file__).resolve().parent
V = D.parent
R = D.parents[3]
BASE = V / 'ipra-current-repaired-six-drift-source-survey'
PLAN = V / 'ipra-frozen-repair-plan-v2' / 'manifest.json'
PEER = Path('/tmp/ipra-current-repaired-build-y6kamkla/state.json')
H = lambda b: hashlib.sha256(b).hexdigest()
inputs = [Path(__file__).resolve(), BASE / 'manifest.json', PLAN, PEER]
before = {str(p): H(p.read_bytes()) for p in inputs}
head_before = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
base, plan, peer = (json.loads(p.read_text()) for p in (BASE / 'manifest.json', PLAN, PEER))
assert base['status'] == 'CANDIDATE_SOURCE_SNAPSHOT' and len(base['sources']) == 1099
assert peer['status'] == 'PASS' and len(peer['records']) == 258
seed = 'ZFCinPA.SeparationKernel'
records = {n: dict(row) for n,row in base['sources'].items()}
path = R / records[seed]['path']
raw = path.read_bytes()
digest = H(raw)
assert digest != records[seed]['sha256'], 'the expected source change is absent'
imports = re.findall(r'^import\s+([A-Z][\w.]*)', raw.decode('utf-8'), re.M)
assert set(imports) - set(records[seed]['imports']) == {'ZFCinPA.ModelCodedSchemaAxioms'}
assert not (set(records[seed]['imports']) - set(imports))
assert all(n in records or n in base['external'] for n in imports)
records[seed] = {'path': records[seed]['path'], 'sha256': digest, 'imports': imports}
def drift():
    result = []
    for n,row in records.items():
        p = R / row['path']
        try: actual = H(p.read_bytes()) if p.is_file() else None
        except OSError: actual = None
        if actual != row['sha256']:
            result.append({'module': n, 'expected': row['sha256'], 'actual': actual})
    return result
initial = drift()
assert not initial, ('workspace moved before source capture', initial)
reachable = set()
queue = [base['target']]
while queue:
    n = queue.pop()
    if n in reachable:
        continue
    reachable.add(n)
    queue.extend(x for x in records[n]['imports'] if x in records)
assert reachable == set(records), ('source graph changed reachability', len(reachable), len(records))
rev = collections.defaultdict(set)
for n,row in records.items():
    for dep in row['imports']:
        rev[dep].add(n)
for node in plan['origin_nodes'].values():
    for dep in node['project_environment']:
        rev[dep].add(node['module'])
for row in peer['records']:
    for dep in row['direct_imports']:
        rev[dep].add(row['name'])
affected = {seed}
queue = [seed]
while queue:
    for owner in rev[queue.pop()]:
        if owner not in affected:
            affected.add(owner)
            queue.append(owner)
assert affected <= set(records), ('recorded environment leaves source graph', sorted(affected - set(records)))
order = list(graphlib.TopologicalSorter({n: [x for x in records[n]['imports'] if x in affected]
                                         for n in sorted(affected)}).static_order())
assert order[-1] == base['target']
snap = D / 'sources'
snap.mkdir()
for n,row in records.items():
    src = (R / row['path']) if n == seed else (BASE / 'sources' / (n.replace('.', '/') + '.lean'))
    assert src.is_file() and not src.is_symlink() and H(src.read_bytes()) == row['sha256'], n
    content = src.read_bytes()
    assert H(content) == row['sha256']
    dest = snap / (n.replace('.', '/') + '.lean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    with dest.open('xb') as out: out.write(content)
    assert dest.is_file() and not dest.is_symlink() and H(dest.read_bytes()) == row['sha256']
assert {str(p): H(p.read_bytes()) for p in inputs} == before
assert all(H((snap / (n.replace('.', '/') + '.lean')).read_bytes()) == row['sha256'] for n,row in records.items())
final = drift()
head_after = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
out = {'status': 'CANDIDATE_SOURCE_SNAPSHOT', 'input_sha256': before, 'sources': records,
       'order': order, 'target': base['target'], 'external': base['external'], 'seed': seed,
       'workspace_drift_before': initial, 'workspace_drift_after': final,
       'head_before': head_before, 'head_after': head_after,
       'boundary': 'Prospective source-only sizing. Current Lean dependencies, matched 107 parent, '
                   'physical project origins, external companions and successor replay require authentication.'}
manifest = D / 'manifest.json'
with manifest.open('x') as f: json.dump(out, f, indent=2, sort_keys=True); f.write('\n')
print('CANDIDATE_SOURCE_SNAPSHOT', len(records), len(order), 'final_drift', len(final), H(manifest.read_bytes()))
