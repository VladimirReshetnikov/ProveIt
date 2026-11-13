"""Reproduce stream-certificate transformations and independent process checks.

This verifier and producer are outside the trusted acceptance programs. Every
acceptance decision below comes from the complete measured checker subprocess.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'fixtures' / 'stream'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    spec = importlib.util.spec_from_file_location('compile_stream', ROOT / 'code' / 'compile_stream.py')
    compiler = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(compiler)
    cases = json.loads((FIXTURES / 'cases.json').read_text())
    transformations = []
    for case in cases:
        if 'source' not in case:
            continue
        source = FIXTURES / case['source']
        tree, before = compiler.parse_old([json.loads(x) for x in source.read_text().splitlines() if x.strip()])
        rows, after = compiler.compile_tree(tree, case['profile'] == 'global')
        raw = ''.join(json.dumps(x, separators=(',', ':')) + '\n' for x in rows).encode()
        expected = FIXTURES / case['file']
        same = raw == expected.read_bytes()
        transformations.append({'source': case['source'], 'target': case['file'],
                                'profile': case['profile'], 'source_rule_counts': before,
                                'target_rule_counts': after, 'target_records': len(rows) - 1,
                                'matches_shipped_fixture': same,
                                'source_sha256': digest(source), 'target_sha256': digest(expected)})
    outcomes = []
    for case in cases:
        profiles = ['local', 'global'] if case['profile'] == 'both' else [case['profile']]
        for profile in profiles:
            program = ROOT / 'code' / ('checker_ast.py' if profile == 'local' else 'checker_tokens.py')
            for optimize in (False, True):
                cmd = [sys.executable, '-I', '-S', '-B']
                if optimize:
                    cmd.append('-O')
                cmd.append(str(program))
                try:
                    result = subprocess.run(cmd, input=(FIXTURES / case['file']).read_bytes(),
                                            capture_output=True, timeout=30)
                    accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
                    timed_out = False
                except subprocess.TimeoutExpired:
                    accepted, timed_out = False, True
                outcomes.append({'fixture': case['file'], 'checker': program.name,
                                 'optimized': optimize, 'expected': case['expected'],
                                 'accepted': accepted, 'timed_out': timed_out,
                                 'passed': accepted == case['expected'] and not timed_out})
    failed = sum(not x['matches_shipped_fixture'] for x in transformations) + sum(not x['passed'] for x in outcomes)
    report = {'scope': 'Finite independent producer replay and subprocess checks; not a proof-assistant verification.',
              'python_version': sys.version.split()[0],
              'checker_sha256': {name: digest(ROOT / 'code' / name) for name in ('checker_ast.py', 'checker_tokens.py')},
              'producer_sha256': digest(ROOT / 'code' / 'compile_stream.py'),
              'transformations': transformations, 'executions': outcomes,
              'transformation_count': len(transformations), 'execution_count': len(outcomes),
              'failed_checks': failed}
    dest = ROOT / 'evidence' / 'stream_verification.json'
    dest.write_text(json.dumps(report, sort_keys=True, indent=2) + '\n')
    print(json.dumps({'transformation_count': len(transformations), 'execution_count': len(outcomes),
                      'failed_checks': failed}, sort_keys=True))
    if failed:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
