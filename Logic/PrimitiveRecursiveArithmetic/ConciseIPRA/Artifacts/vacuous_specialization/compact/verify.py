"""Matched verification of the eager selector on computation-leaf checkers."""
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
CONTROL = ROOT / 'control474.py'
CANDIDATE = ROOT / 'checker473.py'
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
        tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT}

def norm(s):
    return ast.unparse(ast.parse(s)) + '\n'

def measure(p):
    s = norm(p.read_text())
    return {'path': str(p.relative_to(ROOT)),
            'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(s).readline)),
            'ast_nodes': len(list(ast.walk(ast.parse(s)))),
            'normalized_bytes': len(s.encode()),
            'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}

def execute(job):
    name, p, mode, data, expected = job
    args = [sys.executable, '-I', '-S', '-B']
    if mode:
        args.append('-O')
    args.append(str(p))
    out = subprocess.run(args, input=data, capture_output=True, timeout=15)
    accepted = out.returncode == 0 and out.stdout == b'ACCEPT\n'
    return {'case': name, 'program': p.name, 'optimized': mode,
            'expected': expected, 'accepted': accepted,
            'passed': accepted == expected}

def main():
    before = CONTROL.read_text()
    after = norm(before.replace('bool(m or 3 % len(a))', 'any((m, 3 % len(a)))'))
    if before.count('bool(m or 3 % len(a))') != 1 or CANDIDATE.read_text() != after:
        raise ValueError('Candidate is not the declared source change')
    fx = ROOT / 'fixtures'
    cases = json.loads((fx / 'cases.json').read_text())
    data = []
    for case in cases:
        name = case['file']
        expected = case['expected']
        p = fx / name
        b = p.read_bytes()
        data.append((name, b, expected))
        if expected:
            x = json.loads(b)
            x[-1] = [[0, [0]], 0]
            data.append(('false_goal_' + name, json.dumps(x).encode(), False))
    data.append(('direct_zero_seed.json', (fx / 'direct_zero_seed.json').read_bytes(), True))
    jobs = [(n, p, o, b, e) for n, b, e in data for p in [CONTROL, CANDIDATE] for o in [False, True]]
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(execute, jobs))
    failures = [r for r in results if not r['passed']]
    report = {'python': sys.version, 'exact_source_change': True,
              'metrics': [measure(CONTROL), measure(CANDIDATE),
                          measure(ROOT / 'reference/control_tokens243.py'),
                          measure(ROOT / 'reference/control_ast264.py')],
              'fixture_cases': len(data), 'executions': len(results),
              'failures': failures, 'results': results}
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
