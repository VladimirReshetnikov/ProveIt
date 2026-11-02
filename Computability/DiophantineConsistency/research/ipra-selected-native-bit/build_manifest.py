#!/usr/bin/env python3
"""Freeze one-overlay selected-checker and native-Boolean-range additions."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

if not __debug__:
    raise RuntimeError('optimized Python is unsupported')

D = Path(__file__).resolve().parent
ROOT = D.parents[3]
BASE = D.parent / 'ipra-selected-refutation-verifier/author-additions.json'
assert hashlib.sha256(BASE.read_bytes()).hexdigest() == 'dae80b2f3bc452f6138da34e5af026c458c7464bdee1b9a1bb9e0d02ca70a7c2'
p = argparse.ArgumentParser()
p.add_argument('--source-commit', required=True)
args = p.parse_args()
assert re.fullmatch('[0-9a-f]{40}', args.source_commit)
m = json.loads(BASE.read_text())
assert len(m['order']) == len(m['sources']) == 10 and m['status'] == 'FROZEN_ADDITIONS'
assert sum(map(len, m['axiom_reports'].values())) == 16

def blob(path):
    return subprocess.run(['git', 'show', args.source_commit + ':' + path], cwd=ROOT,
                          check=True, capture_output=True).stdout

# A new commit must retain all ten prior source blobs exactly; it is not
# enough for the appended client alone to be tracked.
for name, item in m['sources'].items():
    data = blob(item['workspace_path'])
    assert hashlib.sha256(data).hexdigest() == item['sha256'], name
    assert (ROOT / item['workspace_path']).read_bytes() == data, name

name = 'DiophantineConsistency.IPRASelectedCheckerNativeBit'
path = D / 'draft-src/IPRASelectedCheckerNativeBit.lean'
rel = str(path.relative_to(ROOT))
data = blob(rel)
assert data == path.read_bytes()
imports = re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$', data.decode(), re.M)
assert imports == ['DiophantineConsistency.IPRASelectedCheckerConsistency']
reports = re.findall(r'^#print axioms ([A-Za-z_][A-Za-z0-9_.\']*)\s*$', data.decode(), re.M)
assert reports == ['nativeBitOfClassical', 'selected_checker_boolean_endpoints']
m['source_commit'] = args.source_commit
m['scope'] = ('Single-overlay historical author extension of the audited AQ29 parent: '
              'rebuild both 13-variable chains, selected bounded checker and '
              'native/standard Boolean-range strengthening. Not paired or current-source.')
m['order'].append(name)
m['sources'][name] = {'workspace_path': rel, 'sha256': hashlib.sha256(data).hexdigest(),
                      'imports': imports}
m['axiom_reports'][name] = [name + '.' + r for r in reports]
assert len(m['order']) == len(m['sources']) == 11
assert sum(map(len, m['axiom_reports'].values())) == 18
out = D / 'author-additions.json'
if out.exists() or out.is_symlink():
    raise ValueError('refusing to overwrite a frozen manifest')
out.write_text(json.dumps(m, indent=2, sort_keys=True) + '\n')
print('SELECTED_NATIVE_BIT_FROZEN_MANIFEST', hashlib.sha256(out.read_bytes()).hexdigest())
