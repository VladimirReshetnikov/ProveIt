#!/usr/bin/env python3
"""Recheck the narrow source and graph observations in this review."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
RECEIPT = ROOT / 'Computability/DiophantineConsistency/research/ipra-standard-aq29/survey-receipt.json'
PARENT = Path('/tmp/ipra-aq29-fresh-source-closure-v2/manifest.json')
HEAD = '55a84e6cc0e5fd58607e42f346d1dcc4303ec70a'
def digest(data):
    return hashlib.sha256(data).hexdigest()

raw = RECEIPT.read_bytes()
assert digest(raw) == 'ab547ca5c13e525f3d3d53ddb6f623aee2dc2cb4e5b508c9ad4a24a68e8fddaa'
r = json.loads(raw)
parent_raw = PARENT.read_bytes()
assert digest(parent_raw) == '63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
p = json.loads(parent_raw)
assert r['workspace_head'] == HEAD and r['status'] == 'PROVISIONAL_MANIFEST_PLAN'
assert not r['additional_untracked'] and not r['additional_modified_against_head']
adds = r['additional_project_modules']
assert len(adds) == len(set(adds)) == 6
available = set(p['sources'])
for name in adds:
    row = r['sources'][name]
    path = row['workspace_path']
    source = (ROOT / path).read_bytes()
    blob = subprocess.run(['git', 'show', f'{HEAD}:{path}'], cwd=ROOT,
                          capture_output=True, check=True).stdout
    assert source == blob and digest(source) == row['source_sha256']
    imports = re.findall(r'^import\s+([^\s]+)', source.decode(), re.M)
    assert imports == row['imports']
    assert all(dep in available or dep in r['external_modules'] for dep in imports)
    available.add(name)
rows = dict(p['sources'])
rows.update(r['sources'])
seen, external, todo = set(), set(), list(r['targets'])
while todo:
    name = todo.pop()
    if name in seen or name in external:
        continue
    if name not in rows:
        external.add(name)
        continue
    seen.add(name)
    todo.extend(rows[name]['imports'])
used = seen & set(p['sources'])
assert len(used) == r['parent_modules_used'] == 1209
assert sorted(set(p['sources']) - used) == r['parent_modules_not_used'] == [
    'DiophantineConsistency.IPRAAQ29NativeChecks']
assert seen - set(p['sources']) == set(adds)
assert sorted(external - set(p['external_modules'])) == r['direct_external_not_in_parent'] == []
print('PASS: six source identities and declared import graph; parent bytes and Lean proof unchecked')
