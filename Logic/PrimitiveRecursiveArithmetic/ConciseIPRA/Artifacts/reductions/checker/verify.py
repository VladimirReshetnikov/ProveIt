"""Replay the selected native public-goal suite and report complete-source metrics."""
from pathlib import Path
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
PROGRAMS = ('control629.py', 'checker621.py', 'checker620.py')
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
           tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(name):
    raw = (ROOT / name).read_bytes()
    source = ast.unparse(ast.parse(raw)) + '\n'
    compile(source, name, 'exec')
    return {'file': name,
            'significant_tokens': sum(t.type not in IGNORED for t in
                tokenize.generate_tokens(io.StringIO(source).readline)),
            'ast_nodes': len(list(ast.walk(ast.parse(source)))),
            'normalized_bytes': len(source.encode()),
            'sha256': hashlib.sha256(raw).hexdigest()}


def main():
    cases = json.loads((ROOT / 'fixtures/cases.json').read_text())
    results = []
    for case in cases:
        payload = (ROOT / 'fixtures' / case['file']).read_bytes()
        for optimized in (False, True):
            for program in PROGRAMS:
                command = [sys.executable, '-I', '-S', '-B']
                if optimized:
                    command.append('-O')
                command.append(str(ROOT / program))
                run = subprocess.run(command, input=payload,
                    capture_output=True, timeout=30)
                accepted = run.returncode == 0 and run.stdout == b'ACCEPT\n'
                results.append({'case': case['file'], 'program': program,
                    'optimized': optimized, 'accepted': accepted,
                    'expected': case['expected'],
                    'passed': accepted == case['expected']})
    report = {'python': sys.version, 'metrics': [measure(p) for p in PROGRAMS],
              'cases': len(cases), 'process_executions': len(results),
              'failures': sum(not r['passed'] for r in results),
              'checks': results,
              'boundary': 'The public native Eq/D goal is checked; the whole certificate alphabet is not checked. Unused JSON prefixes remain inert.',
              'limits': 'Finite tests supplement the written simulation argument and do not prove iPRA bi-interpretability or source-size minimality.'}
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    (ROOT / 'metrics.json').write_text(json.dumps(report['metrics'], indent=2) + '\n')
    print(json.dumps({k: report[k] for k in
        ('metrics', 'cases', 'process_executions', 'failures')}, indent=2))
    if report['failures']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
