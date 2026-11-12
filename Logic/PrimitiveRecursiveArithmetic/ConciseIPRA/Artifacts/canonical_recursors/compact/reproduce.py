#!/usr/bin/env python3
"""Measure complete modules and replay the frozen canonical/control fixtures."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENDMARKER, tokenize.ENCODING, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw.decode())
    normalized = (ast.unparse(tree) + '\n').encode()
    tokens = [t for t in tokenize.generate_tokens(
        io.StringIO(normalized.decode()).readline) if t.type not in SKIP]
    compressed = gzip.compress(normalized, compresslevel=9, mtime=0)
    return {'file': path.relative_to(ROOT).as_posix(),
            'raw_bytes': len(raw), 'normalized_bytes': len(normalized),
            'significant_tokens': len(tokens),
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
            'gzip9_normalized_bytes': len(compressed),
            'sha256_raw': hashlib.sha256(raw).hexdigest()}, compressed


def run(program, payload, optimized=False):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(ROOT / program))
    result = subprocess.run(command, input=payload, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, timeout=30)
    return result.returncode == 0 and result.stdout == b'ACCEPT\n'


def main():
    provenance = json.loads((ROOT / 'evidence/provenance.json').read_text())
    for name, record in provenance['reference_hashes'].items():
        data = (ROOT / 'reference' / name).read_bytes()
        blob = b'blob ' + str(len(data)).encode() + b'\0' + data
        if hashlib.sha1(blob).hexdigest() != record['git_blob_sha1']:
            raise ValueError('Frozen reference changed: ' + name)
    metrics = []
    for path in sorted((ROOT / 'code').glob('*.py')) + sorted((ROOT / 'reference').glob('*.py')):
        record, compressed = measure(path)
        metrics.append(record)
        if path.parent.name == 'code':
            path.with_suffix('.py.gz').write_bytes(compressed)
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(
        {'python': sys.version.split()[0], 'modules': metrics}, indent=2) + '\n')

    programs = [
        ('reference/checker_bytes.py', 'local', False),
        ('code/checker_exact.py', 'local', False),
        ('code/checker_compact.py', 'local', False),
        ('code/checker_compact_zero.py', 'zero', False),
        ('code/checker_ast_zero.py', 'zero', False),
        ('code/checker_strict_control.py', 'zero', True),
        ('code/checker_strict.py', 'zero', True),
    ]
    cases = json.loads((ROOT / 'fixtures/cases.json').read_text())
    checks = []
    for optimized in (False, True):
        for program, convention, strict in programs:
            for case in cases:
                expected = case['expected'] and (not strict or case['public_goal'])
                payload = (ROOT / 'fixtures' / convention / case['file']).read_bytes()
                accepted = run(program, payload, optimized)
                checks.append({'program': program, 'case': case['name'],
                               'optimized': optimized, 'expected': expected,
                               'accepted': accepted, 'passed': accepted == expected})

    # The strict interface charges a complete integer/list certificate parser.
    good = json.loads((ROOT / 'fixtures/zero/computation_zero_local.json').read_text())
    for value in ('', 'x', None, True, 0.5, float('nan'), float('inf')):
        # These unused prefixes are intentionally rejected by the strict parser.
        payload = json.dumps([value] + good).encode()
        for program in ('code/checker_strict_control.py', 'code/checker_strict.py'):
            accepted = run(program, payload)
            checks.append({'program': program, 'case': 'strict_prefix_' + repr(value),
                           'expected': False, 'accepted': accepted, 'passed': not accepted})

    # A small real witness-opening proof. It detects the invalid entry-only
    # replacement of k by 1-len(g) before the continuation's scope is extended.
    opening = [[[], 0, [-1], 0], [[], 0, 0, 0], [[[0, 5, 0], 3]]]
    payload = json.dumps(opening).encode()
    for program in ('reference/checker_bytes.py', 'code/checker_exact.py',
                    'code/checker_compact.py'):
        accepted = run(program, payload)
        checks.append({'program': program, 'case': 'used_fresh_parameter',
                       'expected': True, 'accepted': accepted, 'passed': accepted})
    report = {'scope': 'Finite regression checks, not a proof-assistant theorem.',
              'python': sys.version.split()[0], 'checks': checks,
              'number_of_checks': len(checks),
              'all_passed': all(check['passed'] for check in checks)}
    (ROOT / 'evidence/validation.json').write_text(json.dumps(report, indent=2) + '\n')
    if not report['all_passed']:
        failed = [check for check in checks if not check['passed']]
        raise AssertionError(json.dumps(failed, indent=2))
    print(json.dumps({'number_of_checks': len(checks), 'all_passed': True,
                      'modules_measured': len(metrics)}, sort_keys=True))


if __name__ == '__main__':
    main()
