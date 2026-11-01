#!/usr/bin/env python3
"""Prospective 14-variable source graph only; this is not a Lean replay."""
import graphlib
import hashlib
import json
from pathlib import Path
import subprocess

D = Path(__file__).resolve().parent
V = D.parent
R = D.parents[3]
SUR = V / 'ipra-current-repaired-survey'
EXTRA = V / 'ipra-current-native14-frozen-extra'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
load = lambda p: json.loads(Path(p).read_text())
inputs = [Path(__file__), SUR / 'survey.py', SUR / 'manifest.json',
          EXTRA / 'manifest.json',
          V / 'ipra-adaptive-native-current-rebase' / 'manifest.json',
          V / 'ipra-frozen-repair-plan-v2' / 'manifest.json',
          Path('/tmp/ipra-frozen-ancestry-repair-6ftdeyrq/state.json')]
before = {str(p): H(p) for p in inputs}
head_before = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
base = load(SUR / 'manifest.json')
previous = load(EXTRA / 'manifest.json')
assert before[str(SUR / 'survey.py')] == base['surveyor_sha256']
source = (SUR / 'survey.py').read_text()
assert source.count('visit(TARGET)') == 1
env = {'__file__': str(SUR / 'survey.py')}
exec(compile(source.split('visit(TARGET)')[0], str(SUR / 'survey.py'), 'exec'), env)
target = 'DiophantineConsistency.IPRACurrentNativeZFCChecks'
env['visit'](target)
current = env['sources']
shared = set(current) & set(base['sources'])
added = set(current) - set(base['sources'])
assert len(current) == 995 and len(shared) == 984 and len(added) == 11
assert added == set(previous['sources'])
assert all(current[n]['sha256'] == base['sources'][n]['sha256'] for n in shared)
assert all(current[n]['sha256'] == previous['sources'][n]['sha256'] for n in added)
assert not (env['external'] - set(base['external']))
order = list(graphlib.TopologicalSorter({
    n: [d for d in current[n]['imports'] if d in added] for n in sorted(added)
}).static_order())
assert order[-1] == target
for n in added:
    snap = EXTRA / 'sources' / (n.replace('.', '/') + '.lean')
    assert snap.is_file() and not snap.is_symlink() and H(snap) == current[n]['sha256']
assert all(H(R / row['path']) == row['sha256'] for row in current.values())
assert {str(p): H(p) for p in inputs} == before
head_after = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
assert head_before == env['observed_head'] == head_after
out = {'status': 'PROSPECTIVE_SOURCE_GRAPH', 'target': target,
       'input_sha256': before, 'observed_head': head_before,
       'sources': current, 'extra_order': order,
       'external': sorted(env['external']),
       'boundary': 'Source/header comparison only. No Lean --deps audit, object '
                   'environment validation, replay, or source-current endpoint is claimed.'}
dest = D / 'manifest.json'
assert not dest.exists(), 'refusing to overwrite an earlier survey'
dest.write_text(json.dumps(out, sort_keys=True, indent=2) + '\n')
print('PROSPECTIVE_SOURCE_GRAPH', len(current), len(shared), len(added), H(dest))
