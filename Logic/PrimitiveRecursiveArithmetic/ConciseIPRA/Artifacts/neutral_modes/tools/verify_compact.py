from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent

def run(program, text, optimized):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(ROOT / program))
    result = subprocess.run(command, input=text, text=True, capture_output=True, timeout=15)
    return {'accepted': result.returncode == 0 and result.stdout == 'ACCEPT\n',
            'returncode': result.returncode,
            'exception': result.stderr.splitlines()[-1].split(':')[0] if result.stderr else None}

def main():
    cases = json.loads((ROOT / 'fixtures/compact_cases.json').read_text())
    configurations = [('controls/checker_bytes461.py', 'expected_control'),
                      ('code/checker_bytes460.py', 'expected_candidate'),
                      ('code/readable_compact.py', 'expected_candidate')]
    results = []
    for case in cases:
        text = (ROOT / case['file']).read_text()
        for optimized in (False, True):
            for program, expectation in configurations:
                actual = run(program, text, optimized)
                results.append({'case': case['name'], 'program': program,
                                'optimized': optimized, 'expected': case[expectation],
                                **actual, 'passed': actual['accepted'] == case[expectation]})
    failures = [r for r in results if not r['passed']]
    report = {'python': sys.version, 'cases': len(cases), 'executions': len(results),
              'failures': failures, 'results': results,
              'scope': 'Finite supporting regressions; universal claims are proved in the report.'}
    (ROOT / 'evidence/compact_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
