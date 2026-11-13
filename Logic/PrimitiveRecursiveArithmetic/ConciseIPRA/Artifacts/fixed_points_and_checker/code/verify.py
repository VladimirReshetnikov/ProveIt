"""Measure complete programs and compare the identical inherited AST protocol.

Run with Python 3.12.14 for the pinned normalized-source figures.
All fixtures are exact attributed upstream files; this harness is not trusted
by either proof checker. Finite tests supplement the written equivalence proof.
"""
from pathlib import Path
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
        tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}


def measure(name):
    raw = (ROOT / name).read_bytes()
    normal = (ast.unparse(ast.parse(raw)) + '\n').encode()
    return dict(file=name, significant_tokens=sum(
        x.type not in SKIP for x in tokenize.generate_tokens(
            io.StringIO(normal.decode()).readline)),
        ast_nodes=sum(1 for _ in ast.walk(ast.parse(normal))),
        normalized_bytes=len(normal), source_sha256=hashlib.sha256(raw).hexdigest(),
        normalized_sha256=hashlib.sha256(normal).hexdigest())


def run(name, data, optimized):
    flags = ['-I', '-S', '-B'] + (['-O'] if optimized else [])
    r = subprocess.run([sys.executable, *flags, str(ROOT / name)], input=data,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10)
    return r.returncode == 0 and r.stdout == b'ACCEPT\n'


def main():
    measurements = [measure(x) for x in ('checker_tokens241.py',
        'control_ast262.py', 'control_tokens242.py')]
    rows = []
    for p in sorted((ROOT / 'fixtures').glob('*.jsonl')):
        positive = p.name.startswith('global_') or p.name == 'direct_successor_zero_initializer.jsonl'
        data = p.read_bytes()
        tests = [(p.name, data, positive)]
        if positive:
            tail = data.split(b'\n', 1)[1]
            tests.append(('false_goal__' + p.name, b'[0,[0]]\n' + tail, False))
        for label, payload, expected in tests:
            for optimized in (False, True):
                outcomes = {name: run(name, payload, optimized) for name in (
                    'checker_tokens241.py', 'control_ast262.py')}
                rows.append(dict(fixture=label, optimized=optimized,
                                 expected=expected, outcomes=outcomes))
    failures = [x for x in rows if any(y != x['expected'] for y in x['outcomes'].values())]
    result = dict(python=sys.version, measurements=measurements,
                  fixture_count=len(list((ROOT/'fixtures').glob('*.jsonl'))),
                  process_executions=2*len(rows), failures=failures, checks=rows,
                  formal_verification=False,
                  guarantee='Written ideal finite trace equivalence; tests are supplementary.')
    (ROOT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('python','measurements','fixture_count',
                                         'process_executions','failures')},indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
