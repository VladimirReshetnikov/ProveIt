"""Measure the complete modules and exercise the inherited 477-byte fixtures.

The tests supplement the proof in PROOF.txt; they do not prove soundness.
Run from any working directory with CPython 3.12.14 for reference metrics.
"""
import ast
from concurrent.futures import ThreadPoolExecutor
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    data = path.read_bytes()
    tree = ast.parse(data.decode())
    normal = ast.unparse(tree) + '\n'
    return {'file': str(path.relative_to(ROOT)),
            'tokens': sum(t.type not in SKIP for t in
                          tokenize.generate_tokens(io.StringIO(normal).readline)),
            'ast_nodes': len(list(ast.walk(tree))),
            'normalized_utf8_bytes': len(normal.encode()),
            'sha256': hashlib.sha256(data).hexdigest(),
            'normalized_sha256': hashlib.sha256(normal.encode()).hexdigest()}


def run_case(case):
    results = []
    for program in ('control/compact477.py', 'code/compact476.py'):
        for optimized in (False, True):
            command = [sys.executable, '-I', '-S', '-B']
            if optimized:
                command.append('-O')
            command.append(str(ROOT / program))
            process = subprocess.run(command,
                input=(ROOT / 'fixtures' / case['file']).read_bytes(),
                capture_output=True, timeout=10)
            accepted = process.returncode == 0 and process.stdout == b'ACCEPT\n'
            results.append({'program': program, 'optimized': optimized,
                            'accepted': accepted,
                            'passed': accepted == case['expected']})
    return {'fixture': case['file'], 'expected': case['expected'], 'results': results}


def main():
    control = (ROOT / 'control/compact477.py').read_text()
    candidate = (ROOT / 'code/compact476.py').read_text()
    old = 'bool(m or 3 % len(a))'
    new = 'any((m, 3 % len(a)))'
    if control.count(old) != 1 or candidate != control.replace(old, new):
        raise SystemExit('The claimed single-expression source relation failed.')
    modules = [ROOT / 'control/compact477.py', ROOT / 'code/compact476.py']
    modules += sorted((ROOT / 'baselines').glob('*.py'))
    metrics = {'python': sys.version, 'normalization': 'ast.unparse + LF',
               'modules': [measure(path) for path in modules]}
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
    cases = json.loads((ROOT / 'fixtures/cases.json').read_text())
    with ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run_case, cases))
    failures = [r for r in results if any(not x['passed'] for x in r['results'])]
    receipt = {'python': sys.version, 'source_relation_verified': True,
               'fixture_count': len(cases), 'process_executions': 4 * len(cases),
               'failures': failures, 'results': results}
    (ROOT / 'evidence/verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'source_relation_verified': True,
                      'fixture_count': len(cases),
                      'process_executions': receipt['process_executions'],
                      'failure_count': len(failures),
                      'candidate_metrics': metrics['modules'][1]}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
