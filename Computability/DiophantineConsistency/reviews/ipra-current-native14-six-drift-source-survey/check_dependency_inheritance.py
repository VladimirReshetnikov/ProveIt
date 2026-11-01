#!/usr/bin/env python3
"""Check the three prior Lean header-dependency receipts cover this snapshot."""
import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parent
V = D.parent
S = V / 'ipra-current-repaired-survey'
B = V / 'ipra-current-repaired-six-drift-source-survey'
O = V / 'ipra-current-native14-source-survey-v2'
P = V / 'ipra-current-repaired-build' / 'manifest.json'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs = [Path(__file__).resolve(), D / 'manifest.json', S / 'manifest.json',
          S / 'lean-deps-receipt.json', S / 'check_lean_deps.py', B / 'manifest.json',
          B / 'lean-deps-receipt.json', O / 'manifest.json', O / 'lean-deps-receipt.json', P, LEAN]
before = {str(p): H(p) for p in inputs}
read = lambda p: json.loads(Path(p).read_text())
cur, orig, base, old, prior, six, extra, parent = [read(p) for p in (
    D / 'manifest.json', S / 'manifest.json', B / 'manifest.json', O / 'manifest.json',
    S / 'lean-deps-receipt.json', B / 'lean-deps-receipt.json', O / 'lean-deps-receipt.json', P)]
assert cur['status'] == base['status'] == 'CANDIDATE_SOURCE_SNAPSHOT'
assert old['status'] == 'PROSPECTIVE_SOURCE_GRAPH'
for p in (B / 'manifest.json', B / 'lean-deps-receipt.json', O / 'manifest.json', O / 'lean-deps-receipt.json'):
    assert cur['input_sha256'][str(p)] == H(p)
assert parent['gate_guard'][str(S / 'lean-deps-receipt.json')] == H(S / 'lean-deps-receipt.json')
assert prior['manifest_sha256'] == H(S / 'manifest.json') and prior['checker_sha256'] == H(S / 'check_lean_deps.py')
assert prior['lean_sha256'] == H(LEAN) and prior['count'] == len(prior['rows']) == 1099 and not prior['errors']
assert set(prior['rows']) == set(orig['sources'])
for receipt in (six, extra):
    assert receipt['status'] == 'PASS_HEADER_DEPS'
    for path, digest in receipt['input_sha256'].items():
        assert H(path) == digest, path
assert six['input_sha256'][str(B / 'manifest.json')] == H(B / 'manifest.json')
assert extra['input_sha256'][str(O / 'manifest.json')] == H(O / 'manifest.json')
shared = set(cur['sources']) & set(base['sources'])
added = set(cur['sources']) - set(base['sources'])
changed = {n for n in shared if base['sources'][n]['sha256'] != orig['sources'][n]['sha256']}
assert len(shared) == 984 and len(added) == 11 and len(changed) == 6
assert set(extra['rows']) == added and changed <= set(six['rows']) and len(six['rows']) == 6
for name, row in cur['sources'].items():
    source = D / 'sources' / (name.replace('.', '/') + '.lean')
    assert source.is_file() and not source.is_symlink() and H(source) == row['sha256'], name
    if name in shared:
        assert row == base['sources'][name]
        if name not in changed:
            assert row == orig['sources'][name] and name in prior['rows']
        else:
            assert name in six['rows'] and row['imports'] == orig['sources'][name]['imports']
    else:
        assert row == old['sources'][name] and name in extra['rows']
assert {str(p): H(p) for p in inputs} == before
assert all(H(D / 'sources' / (n.replace('.', '/') + '.lean')) == row['sha256'] for n,row in cur['sources'].items())
out = {'status': 'PASS_DEPENDENCY_RECEIPT_COVERAGE', 'input_sha256': before,
       'unchanged_shared_count': len(shared) - len(changed), 'changed_shared_count': len(changed),
       'additional_count': len(added), 'changed': sorted(changed),
       'boundary': 'Composes recorded Lean --deps header checks by identical source bytes and import lists; '
                   'does not authenticate project objects, dynamic imports or a successor proof.'}
path = D / 'dependency-inheritance-receipt.json'
with path.open('x') as f:
    json.dump(out, f, indent=2, sort_keys=True)
    f.write('\n')
print('PASS_DEPENDENCY_RECEIPT_COVERAGE', len(cur['sources']), H(path))
