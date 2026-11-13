"""Reproduce the literal source transformation, whole-module metrics and fixtures."""
from pathlib import Path
import ast
import concurrent.futures
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
        tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT}


def normalize(source):
    return ast.unparse(ast.parse(source)) + '\n'


def measure(path):
    source = normalize(path.read_text())
    return {'file': path.name,
            'tokens': sum(t.type not in SKIP for t in
                          tokenize.generate_tokens(io.StringIO(source).readline)),
            'ast_nodes': len(list(ast.walk(ast.parse(source)))),
            'normalized_bytes': len(source.encode()),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def run(task):
    case, name, optimized = task
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(ROOT / name))
    process = subprocess.run(command,
        input=(ROOT / 'fixtures' / case['file']).read_bytes(),
        capture_output=True, timeout=15)
    accepted = process.returncode == 0 and process.stdout == b'ACCEPT\n'
    return {'fixture': case['file'], 'program': name, 'optimized': optimized,
            'expected': case['expected'], 'accepted': accepted,
            'passed': accepted == case['expected']}


def main():
    control = (ROOT / 'control477.py').read_text()
    assert control.count('bool(m or 3 % len(a))') == 1
    transformed = normalize(control.replace('bool(m or 3 % len(a))',
                                            'any((m, 3 % len(a)))'))
    if transformed != (ROOT / 'compact476.py').read_text():
        raise ValueError('Candidate is not the declared exact transformation')
    cases = json.loads((ROOT / 'fixtures/cases.json').read_text())
    tasks = [(case, program, optimized) for case in cases
             for program in ('control477.py', 'compact476.py')
             for optimized in (False, True)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run, tasks))
    failures = [row for row in results if not row['passed']]
    report = {'python': sys.version, 'exact_transformation_verified': True,
              'metrics': [measure(ROOT / name) for name in
                          ('control477.py', 'compact476.py')],
              'fixture_count': len(cases), 'process_executions': len(results),
              'failures': failures, 'results': results}
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
