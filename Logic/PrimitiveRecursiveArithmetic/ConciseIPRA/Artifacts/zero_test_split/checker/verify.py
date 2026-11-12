"""Regression checks for the guarded-only 478-byte scope-header experiment.

This is an untrusted harness. It is not imported by the acceptance module.
Run from the task workspace with Python 3.12.14.
"""
import ast
import concurrent.futures
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

HERE = Path(__file__).resolve().parent
BASE = HERE
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def shift(value, amount):
    if type(value) is int and value < 0:
        return value + amount
    if type(value) is list:
        return [shift(child, amount) for child in value]
    return value


def execute(task):
    source, payload, expected, label, optimized = task
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(source))
    result = subprocess.run(command, input=json.dumps(payload).encode(),
                            capture_output=True, timeout=20)
    actual = result.returncode == 0 and result.stdout == b'ACCEPT\n'
    return {'case': label, 'optimized': optimized, 'expected': expected,
            'accepted': actual, 'passed': actual == expected}


def main():
    tasks = []
    for group in ('compact_context', 'compact_progress'):
        for case in json.loads((BASE / 'fixtures' / group / 'cases.json').read_text()):
            payload = json.loads((BASE / 'fixtures' / group / case['file']).read_text())
            for optimized in (False, True):
                tasks.append((BASE / 'controls/compact479.py', payload,
                              case['expected'], group + '/' + case['file'] + '/control', optimized))
                readable_payload = payload[:-1] + [[payload[-1], 0]]
                tasks.append((HERE / 'code/readable.py', readable_payload,
                              case['expected'], group + '/' + case['file'] + '/readable', optimized))
                for offset in (0, -3):
                    updated = shift(payload, offset)
                    updated[-1] = [updated[-1], offset]
                    tasks.append((HERE / 'code/compact478.py', updated,
                                  case['expected'], group + '/' + case['file'] + '/floor' + str(offset), optimized))
    positive_cases = ('guarded_induction_with_used_hypothesis_local.json',
                      'guarded_literal_equation_introduction_local.json',
                      'guarded_lift_elimination_local.json')
    for name in positive_cases:
        payload = json.loads((BASE / 'fixtures/compact_context' / name).read_text())
        for floor in (1, 2, 5):
            updated = payload[:-1] + [[payload[-1], floor]]
            for optimized in (False, True):
                tasks.append((HERE / 'code/compact478.py', updated, False,
                              'positive_floor/' + name + '/' + str(floor), optimized))
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        rows = list(pool.map(execute, tasks))
    metrics = []
    for path in (BASE / 'controls/compact479.py', HERE / 'code/compact478.py'):
        source = ast.unparse(ast.parse(path.read_text())) + '\n'
        metrics.append({'name': path.name,
                        'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(source).readline)),
                        'ast_nodes': len(list(ast.walk(ast.parse(source)))),
                        'normalized_bytes': len(source.encode())})
    report = {'python': sys.version, 'metrics': metrics, 'executions': len(rows),
              'failures': [row for row in rows if not row['passed']],
              'results': rows,
              'scope': 'Guarded public grammar is an external interface condition, exactly as for compact479. This is not a full-native or all-JSON soundness claim.'}
    (HERE / 'compact478_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
    if report['failures']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
