#!/usr/bin/env python3
"""Capture all current source drift after matched 120-module replay."""
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
BASE = V / 'ipra-current-repaired-post159-final-source-survey'
PLAN = V / 'ipra-frozen-repair-plan-v2' / 'manifest.json'
OLD = Path('/tmp/ipra-current-repaired-build-y6kamkla/state.json')
PEER = Path('/tmp/ipra-six-drift-replay-42b7hj5k/state.json')
P172 = Path('/tmp/ipra-eleven-drift-replay-sfz0zyj0/state.json')
P159 = Path('/tmp/ipra-post172-replay-81f0339y/state.json')
P120 = Path('/tmp/ipra-post159-replay-6c04l2wf/state.json')
A120 = Path('/tmp/ipra-post159-replay-xof0w15j/state.json')
C120A = V / 'ipra-current-repaired-post159-verification' / 'receipt.json'
C120B = V / 'ipra-current-repaired-post159-verification-peer' / 'receipt.json'
O120 = V / 'ipra-current-repaired-post159-terminal-observations'
W120 = V / 'ipra-current-repaired-post159-comparator-terminal-observations'
CA = V / 'ipra-current-repaired-six-drift-verification' / 'receipt.json'
CB = V / 'ipra-current-repaired-six-drift-verification-peer' / 'receipt.json'
H = lambda b: hashlib.sha256(b).hexdigest()
inputs = [Path(__file__).resolve(), BASE / 'manifest.json', PLAN, OLD, PEER, P172, P159, P120, A120, CA, CB, C120A, C120B, O120/'author.json', O120/'peer.json', W120/'author.json', W120/'peer.json', C120A.parent/'terminal.json', C120B.parent/'terminal.json']
before = {str(p): H(p.read_bytes()) for p in inputs}
head_before = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
base, plan, old, peer, a, b = (json.loads(p.read_text()) for p in (BASE / 'manifest.json', PLAN, OLD, PEER, CA, CB))
assert base['status'] == 'CANDIDATE_SOURCE_SNAPSHOT' and len(base['sources']) == 1099
assert old['status'] == 'PASS' and len(old['records']) == 258
assert peer['status'] == 'PASS' and len(peer['records']) == 107
parent172 = json.loads(P172.read_text())
assert parent172['status'] == 'PASS' and len(parent172['records']) == 172
parent159=json.loads(P159.read_text())
assert parent159['status']=='PASS' and len(parent159['records'])==159
parent120=json.loads(P120.read_text());assert parent120['status']=='PASS' and len(parent120['records'])==120
ca120=json.loads(C120A.read_text());cb120=json.loads(C120B.read_text());assert ca120==cb120 and ca120['status']=='MATCHED_PASS' and ca120['rows']==120 and ca120['peer_state_sha256']==H(P120.read_bytes()) and ca120['author_state_sha256']==H(A120.read_bytes()) and json.loads(A120.read_text())['status']=='PASS'
for path in (O120/'author.json',O120/'peer.json',W120/'author.json',W120/'peer.json'):
 ob=json.loads(path.read_text());assert ob['tool_session'] and ob['observed_exit_code']==0
assert json.loads((O120/'peer.json').read_text())['state_sha256']==H(P120.read_bytes())
assert json.loads((O120/'author.json').read_text())['state_sha256']==H(A120.read_bytes())
for path,receipt in ((W120/'author.json',C120A),(W120/'peer.json',C120B)):
 assert json.loads(path.read_text())['receipt_sha256']==H(receipt.read_bytes()) and json.loads(path.read_text())['terminal_sha256']==H((receipt.parent/'terminal.json').read_bytes()) and json.loads((receipt.parent/'terminal.json').read_text())['status']=='PASS_COMPARATOR_EXIT_0'
assert a == b and a['status'] == 'MATCHED_PASS' and a['rows'] == 107
assert a['peer_state_sha256'] == H(PEER.read_bytes())
seeds = {n for n,row in base['sources'].items() if not (R / row['path']).is_file() or H((R / row['path']).read_bytes()) != row['sha256']}
known = {'DiophantineConsistency.PRAQCompatibility','ZFCinPA.CollectionTemplate254','ZFCinPA.LDriverBase','ZFCinPA.LGlue4','ZFCinPA.LReplBase','ZFCinPA.LStepExT','ZFCinPA.OpenSetTemplateCompiler','ZFCinPA.SeparationKernel','ZFCinPA.SetPlaceholders'}
assert known <= seeds, ('known drift unexpectedly absent', sorted(known-seeds))
records = {n: dict(row) for n,row in base['sources'].items()}
for n in seeds:
    path = R / records[n]['path']
    raw = path.read_bytes()
    digest = H(raw)
    assert digest != records[n]['sha256'], ('expected change absent', n)
    imports = re.findall(r'^import\s+([A-Z][\w.]*)', raw.decode('utf-8'), re.M)
    old_imports = records[n]['imports']
    assert all(x in records or x in base['external'] for x in imports)
    records[n] = {'path': records[n]['path'], 'sha256': digest, 'imports': imports}
def drift():
    out = []
    for n,row in records.items():
        p = R / row['path']
        try: actual = H(p.read_bytes()) if p.is_file() else None
        except OSError: actual = None
        if actual != row['sha256']:
            out.append({'module': n, 'expected': row['sha256'], 'actual': actual})
    return out
initial = drift()
assert not initial, ('workspace moved before source capture', initial)
reachable = set()
queue = [base['target']]
while queue:
    n = queue.pop()
    if n in reachable: continue
    reachable.add(n)
    queue.extend(x for x in records[n]['imports'] if x in records)
assert reachable == set(records), ('source graph reachability changed', len(reachable))
rev = collections.defaultdict(set)
for n,row in records.items():
    for dep in row['imports']: rev[dep].add(n)
for node in plan['origin_nodes'].values():
    for dep in node['project_environment']: rev[dep].add(node['module'])
for state in (old,peer,parent172,parent159,parent120):
    for row in state['records']:
        for dep in row['direct_imports']: rev[dep].add(row['name'])
affected = set(seeds)
queue = list(seeds)
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
    src = (R / row['path']) if n in seeds else (BASE / 'sources' / (n.replace('.', '/') + '.lean'))
    assert src.is_file() and not src.is_symlink() and H(src.read_bytes()) == row['sha256'], n
    content = src.read_bytes()
    assert H(content) == row['sha256']
    dest = snap / (n.replace('.', '/') + '.lean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    with dest.open('xb') as f: f.write(content)
    assert dest.is_file() and not dest.is_symlink() and H(dest.read_bytes()) == row['sha256']
assert {str(p): H(p.read_bytes()) for p in inputs} == before
assert all(H((snap / (n.replace('.', '/') + '.lean')).read_bytes()) == row['sha256'] for n,row in records.items())
final = drift()
head_after = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
out = {'status': 'CANDIDATE_SOURCE_SNAPSHOT', 'input_sha256': before, 'sources': records,
       'order': order, 'target': base['target'], 'external': base['external'], 'seeds': sorted(seeds),
       'workspace_drift_before': initial, 'workspace_drift_after': final,
       'head_before': head_before, 'head_after': head_after,
       'boundary': 'Prospective source-only sizing; the matched 120 peer direct-input edges are incorporated; physical origins and replay remain open. Current Lean dependencies, physical project '
                   'origins, external companions and successor replay require authentication.'}
manifest = D / 'manifest.json'
with manifest.open('x') as f: json.dump(out, f, indent=2, sort_keys=True); f.write('\n')
print('CANDIDATE_SOURCE_SNAPSHOT', len(records), len(order), 'final_drift', len(final), H(manifest.read_bytes()))
