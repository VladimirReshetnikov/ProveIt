"""Reproduce the fully validated native checker comparison (standard library)."""
from pathlib import Path
import ast
import copy
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def metrics(path):
    tree = ast.parse(path.read_text())
    normalized = ast.unparse(tree) + '\n'
    return {'file': path.name, 'bytes': len(normalized.encode()),
            'tokens': sum(t.type not in SKIP for t in
                          tokenize.generate_tokens(io.StringIO(normalized).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def run(path, payload, optimized=False):
    result = subprocess.run([sys.executable, '-I', '-S', '-B'] +
                            (['-O'] if optimized else []) + [str(path)],
                            input=payload, capture_output=True, timeout=30)
    return result.returncode == 0 and result.stdout == b'ACCEPT\n'


def exact_tree(value):
    return type(value) is int or (type(value) is list and all(map(exact_tree, value)))


provenance = json.loads((ROOT / 'PROVENANCE.json').read_text())
for row in provenance['controls'] + provenance['fixtures']:
    content = (ROOT / row['local_path']).read_bytes()
    assert hashlib.sha256(content).hexdigest() == row['sha256'], row['local_path']
    assert hashlib.sha1(b'blob ' + str(len(content)).encode() + b'\0' + content).hexdigest() == row['git_blob']

control = ROOT / 'control849.py'
candidate = ROOT / 'checker.py'
rows = json.loads((ROOT / 'fixtures/cases.json').read_text())
checks = []
for row in rows:
    payload = (ROOT / 'fixtures' / row['file']).read_bytes()
    for optimized in (False, True):
        left = run(control, payload, optimized)
        right = run(candidate, payload, optimized)
        assert left == right, (row['name'], optimized, left, right)
        checks.append({'case': row['name'], 'optimized': optimized, 'accepted': right})

# These cases establish the whole-document boundary, including inactive data.
valid = json.loads((ROOT / 'fixtures/computation_zero_local.json').read_text())
assert run(candidate, json.dumps(valid).encode())
bad_leaves = [None, False, True, 0.0, 1.0, -0.5, '', '123', '[]', {}, {'a': 0}]
prefix_checks = []
for leaf in bad_leaves:
    for prefix in (leaf, [0, [leaf]]):
        payload = json.dumps([prefix] + valid).encode()
        assert not run(candidate, payload), prefix
        assert not run(control, payload), prefix
        prefix_checks.append({'prefix': prefix, 'accepted': False})
for prefix in (0, [], [1, -4, [0, 3, []]]):
    payload = json.dumps([prefix] + valid).encode()
    assert run(candidate, payload), prefix
    assert run(control, payload), prefix
    prefix_checks.append({'prefix': prefix, 'accepted': True})

# Whole-driver failures, including scalar strings consisting of allowed chars.
root_checks = []
for document in (None, False, True, 0, 123, '123', '[]', ' -1,2 ', {}, {'a': 0}):
    payload = json.dumps(document).encode()
    assert not run(candidate, payload), document
    root_checks.append({'document': document, 'accepted': False})

# Check the whitelist against an independent recursive type predicate on parsed
# JSON lists. This is supplementary; the general type proof is in AUDIT.txt.
alphabet_checks = 0
leaves = bad_leaves + [0, 1, -1, 10000000000000000000, [], [0], [1, -2]]
for a in leaves:
    for b in leaves:
        for value in ([a, b], [[a], [b]], [a, [0, [b]]]):
            parsed = json.loads(json.dumps(value))
            gate = not str(parsed).strip('0123456789-[], ')
            assert gate == exact_tree(parsed), parsed
            alphabet_checks += 1

report = {'python': sys.version, 'all_passed': True,
          'frozen_control_and_fixture_blobs_verified': len(provenance['controls']) + len(provenance['fixtures']),
          'fixture_cli_pairs': len(checks), 'fixture_cli_processes': 2 * len(checks),
          'invalid_prefix_cases': 2 * len(bad_leaves), 'valid_prefix_cases': 3,
          'invalid_top_level_cases': len(root_checks), 'alphabet_comparisons': alphabet_checks,
          'metrics': [metrics(control), metrics(ROOT / 'control656.py'), metrics(candidate)],
          'fixture_checks': checks, 'prefix_checks': prefix_checks, 'root_checks': root_checks,
          'scope': 'Finite regression evidence, not a proof-assistant verification or proof of global minimality.'}
(ROOT / 'validation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k not in
                  ('fixture_checks', 'prefix_checks', 'root_checks')}, indent=2))
