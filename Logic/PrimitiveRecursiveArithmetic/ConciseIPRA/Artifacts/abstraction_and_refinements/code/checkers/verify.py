"""Reproduce complete-module sizes and matched certificate checks."""
import ast
import concurrent.futures
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
           tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}


def measure(path):
    source = ast.unparse(ast.parse(path.read_text())) + '\n'
    return {'file': path.name,
            'tokens': sum(t.type not in IGNORED for t in
                          tokenize.generate_tokens(io.StringIO(source).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(source))),
            'normalized_bytes': len(source.encode()),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def run(case):
    results = []
    for variant in ('control', 'checker'):
        path = ROOT / (case['profile'] + '_' + variant + '.py')
        for optimized in (False, True):
            cmd = [sys.executable, '-I', '-S', '-B']
            if optimized:
                cmd.append('-O')
            cmd.append(str(path))
            try:
                p = subprocess.run(cmd, input=(ROOT / case['file']).read_bytes(),
                                   capture_output=True, timeout=10)
                accepted = p.returncode == 0 and p.stdout == b'ACCEPT\n'
                item = {'program': path.name, 'optimized': optimized,
                        'accepted': accepted, 'passed': accepted == case['expected']}
            except subprocess.TimeoutExpired:
                item = {'program': path.name, 'optimized': optimized,
                        'accepted': False, 'passed': False, 'timeout': True}
            results.append(item)
    return dict(case, results=results)


def main():
    base_cases = json.loads((ROOT / 'fixtures/cases.json').read_text())
    profiles = ['compact', 'native_tokens', 'native_ast', 'native_bytes',
                'strict_tokens', 'strict_ast', 'strict_bytes']
    cases = [dict(case, profile=profile)
             for profile in profiles for case in base_cases
             if profile.split('_')[0] == case['profile']]
    if any(type(case['expected']) is not bool for case in cases):
        raise ValueError('Every fixture needs an explicit Boolean expectation')
    metrics = [measure(ROOT / (profile + '_' + variant + '.py'))
               for profile in profiles
               for variant in ('control', 'checker')]
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run, cases))
    failures = [r for r in results if any(not x['passed'] for x in r['results'])]
    report = {'python': sys.version, 'normalization': 'ast.unparse plus LF',
              'metrics': metrics, 'fixture_count': len(cases),
              'isolated_executions': 4 * len(cases), 'failures': failures,
              'results': results}
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
