#!/usr/bin/env python3
"""Compose the prior 14-source and new header dependency receipts by hash."""
import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parent
V = D.parent
OLD = V / 'ipra-current-native14-six-drift-source-survey'
BASE = V / 'ipra-current-repaired-seven-drift-source-survey'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
files = [Path(__file__).resolve(), D / 'manifest.json', OLD / 'manifest.json',
         OLD / 'dependency-inheritance-receipt.json', BASE / 'manifest.json',
         BASE / 'lean-deps-receipt.json']
before = {str(p): H(p) for p in files}
read = lambda p: json.loads(Path(p).read_text())
cur, old, prior, base, fresh = [read(p) for p in (D / 'manifest.json', OLD / 'manifest.json',
    OLD / 'dependency-inheritance-receipt.json', BASE / 'manifest.json', BASE / 'lean-deps-receipt.json')]
assert cur['status'] == old['status'] == base['status'] == 'CANDIDATE_SOURCE_SNAPSHOT'
assert prior['status'] == 'PASS_DEPENDENCY_RECEIPT_COVERAGE' and fresh['status'] == 'PASS_HEADER_DEPS'
for p in (OLD / 'manifest.json', OLD / 'dependency-inheritance-receipt.json',
          BASE / 'manifest.json', BASE / 'lean-deps-receipt.json'):
    assert cur['input_sha256'][str(p)] == H(p)
assert prior['input_sha256'][str(OLD / 'manifest.json')] == H(OLD / 'manifest.json')
assert fresh['input_sha256'][str(BASE / 'manifest.json')] == H(BASE / 'manifest.json')
for receipt in (prior, fresh):
    for path, digest in receipt['input_sha256'].items():
        assert H(path) == digest, path
seed = 'ZFCinPA.SeparationKernel'
assert fresh['module'] == base['seed'] == seed
assert hashlib.sha256(fresh['stdout'].encode()).hexdigest() == fresh['stdout_sha256']
assert len(cur['sources']) == 995 and set(cur['sources']) == set(old['sources'])
for n,row in cur['sources'].items():
    path = D / 'sources' / (n.replace('.', '/') + '.lean')
    assert path.is_file() and not path.is_symlink() and H(path) == row['sha256'], n
    if n == seed:
        assert row == base['sources'][n] and row['sha256'] != old['sources'][n]['sha256']
    else:
        assert row == old['sources'][n], n
assert {str(p): H(p) for p in files} == before
assert all(H(D / 'sources' / (n.replace('.', '/') + '.lean')) == row['sha256'] for n,row in cur['sources'].items())
out = {'status': 'PASS_DEPENDENCY_RECEIPT_COVERAGE', 'input_sha256': before,
       'unchanged_count': 994, 'changed_count': 1, 'changed': seed,
       'boundary': 'Composes recorded Lean --deps header checks by identical source bytes and import lists; '
                   'does not authenticate project objects, dynamic imports or a successor proof.'}
path = D / 'dependency-inheritance-receipt.json'
with path.open('x') as f: json.dump(out, f, indent=2, sort_keys=True); f.write('\n')
print('PASS_DEPENDENCY_RECEIPT_COVERAGE', len(cur['sources']), H(path))
