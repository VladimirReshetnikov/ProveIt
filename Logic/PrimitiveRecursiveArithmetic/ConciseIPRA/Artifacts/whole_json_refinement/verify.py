"""Reproduce complete-module sizes and framing simulation on inherited fixtures.

This harness is not imported by any acceptance program. The two candidate
modules are complete standalone checkers; the controls read JSON records.
"""
import ast
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
OMIT = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
        tokenize.DEDENT, tokenize.COMMENT, tokenize.ENDMARKER}


def measure(path):
    normalized = ast.unparse(ast.parse(path.read_text())) + '\n'
    return {'tokens': sum(t.type not in OMIT for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
            'bytes': len(normalized.encode()),
            'normalized_sha256': hashlib.sha256(normalized.encode()).hexdigest()}


def execute(path, data, optimized):
    cmd = [sys.executable, '-I', '-S', '-B']
    if optimized:
        cmd.append('-O')
    result = subprocess.run(cmd + [str(path)], input=data, capture_output=True, timeout=30)
    return result.returncode == 0 and result.stdout == b'ACCEPT\n'


def main():
    pairs = {'local': ('code/checker_ast268.py', 'reference/checker_ast.py'),
             'global': ('code/checker_tokens248.py', 'reference/checker_tokens.py')}
    paths = sorted({path for pair in pairs.values() for path in pair})
    measurements = {path: measure(ROOT / path) for path in paths}
    outcomes = []
    for case in json.loads((ROOT / 'fixtures/cases.json').read_text()):
        data = (ROOT / 'fixtures' / case['file']).read_bytes()
        values = json.loads(data)
        stream = ''.join(json.dumps(value) + '\n' for value in reversed(values)).encode()
        profiles = pairs if case['profile'] == 'both' else [case['profile']]
        for profile in profiles:
            candidate, control = pairs[profile]
            for optimized in (False, True):
                actual = execute(ROOT / candidate, data, optimized)
                reference = execute(ROOT / control, stream, optimized)
                outcomes.append({'fixture': case['file'], 'profile': profile,
                                 'optimized': optimized, 'expected': case['expected'],
                                 'candidate_accepted': actual, 'control_accepted': reference,
                                 'passed': actual == reference == case['expected']})
    result = {'python_version': sys.version.split()[0],
              'scope': 'Finite regression evidence, accompanying the universal framing simulation proof; not formal verification.',
              'measurements': measurements,
              'fixture_count': len(json.loads((ROOT / 'fixtures/cases.json').read_text())),
              'paired_comparisons': len(outcomes), 'process_executions': 2 * len(outcomes),
              'failed_checks': sum(not row['passed'] for row in outcomes),
              'outcomes': outcomes}
    (ROOT / 'evidence/verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in ('python_version', 'measurements', 'fixture_count', 'paired_comparisons', 'process_executions', 'failed_checks')}, indent=2))
    if result['failed_checks']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
