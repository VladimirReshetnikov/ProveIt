"""Reproduce candidate metrics and matched-contract regression fixtures.

The six measured checker modules import no helper from this package.
Use CPython 3.12.14 for exactly the reference AST/unparse/token convention.
"""
import ast
import concurrent.futures
import hashlib
import io
import json
import pathlib
import subprocess
import sys
import tokenize

ROOT = pathlib.Path(__file__).resolve().parent
IGNORE = {tokenize.ENCODING, tokenize.NEWLINE, tokenize.NL,
          tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER, tokenize.COMMENT}
EXPECTED = {
    'controls/compact487.py': (276, 308, 487),
    'code/compact479.py': (272, 304, 479),
    'controls/native629.py': (324, 374, 629),
    'code/native607.py': (337, 383, 607),
    'controls/strict646.py': (343, 392, 646),
    'code/strict637.py': (344, 392, 637),
}


def metric(name):
    raw = (ROOT / name).read_bytes()
    normalized = ast.unparse(ast.parse(raw)) + '\n'
    compile(normalized, name, 'exec')
    counts = (sum(t.type not in IGNORE for t in
                  tokenize.generate_tokens(io.StringIO(normalized).readline)),
              len(list(ast.walk(ast.parse(normalized)))), len(normalized.encode()))
    return {'file': name, 'tokens': counts[0], 'ast_nodes': counts[1],
            'normalized_bytes': counts[2], 'expected': EXPECTED[name],
            'matched': counts == EXPECTED[name],
            'sha256': hashlib.sha256(raw).hexdigest()}


def run(task):
    cmd = [sys.executable, '-I', '-S', '-B']
    if task['optimized']:
        cmd.append('-O')
    cmd.append(str(ROOT / task['program']))
    payload = (ROOT / task['fixture']).read_bytes()
    proc = subprocess.run(cmd, input=payload, capture_output=True, timeout=30)
    accepted = proc.returncode == 0 and proc.stdout == b'ACCEPT\n'
    return {**task, 'accepted': accepted, 'passed': accepted == task['expected'],
            'fixture_sha256': hashlib.sha256(payload).hexdigest()}


def main():
    groups = [
        ('compact_context', ['controls/compact487.py', 'code/compact479.py']),
        ('compact_progress', ['controls/compact487.py', 'code/compact479.py']),
        ('native', ['controls/native629.py', 'code/native607.py']),
        ('strict_proofs', ['controls/strict646.py', 'code/strict637.py']),
        ('strict_boundary', ['controls/strict646.py', 'code/strict637.py']),
    ]
    tasks = []
    for group, programs in groups:
        for case in json.loads((ROOT / 'fixtures' / group / 'cases.json').read_text()):
            for program in programs:
                for optimized in (False, True):
                    tasks.append({'program': program,
                                  'fixture': 'fixtures/' + group + '/' + case['file'],
                                  'expected': case['expected'],
                                  'optimized': optimized})
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run, tasks))
    failures = [x for x in results if not x['passed']]
    metrics = [metric(p) for p in EXPECTED]
    report = {'python': sys.version, 'metrics': metrics, 'executions': len(results),
              'failures': failures, 'results': results,
              'scope': 'Finite evidence supplements the universal simulation proofs.'}
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'results'}, indent=2))
    if failures or not all(m['matched'] for m in metrics):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
