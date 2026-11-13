"""Process-level regression and framing checks for the measured refinement.

The original fixture expectations are frozen upstream evidence. The paired
comparison supplements, and does not replace, the written simulation proof.
"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
CONTROL = 'reference/checker_sorted_556.py'
CANDIDATE = 'code/checker_sorted_line.py'


def run(job):
    path, name, data, expected, optimized = job
    result = subprocess.run(
        [sys.executable, *(['-O'] if optimized else []), str(ROOT / path)],
        input=data, text=True, capture_output=True, timeout=20)
    accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
    return {'path': path, 'case': name, 'optimized': optimized,
            'expected': expected, 'accepted': accepted,
            'pass': accepted == expected, 'exit_code': result.returncode}


def main():
    cases = json.loads((ROOT / 'tests/inherited112.json').read_text())['cases']
    jobs = []
    for case in cases:
        data = json.dumps(case['certificate'], separators=(',', ':')) + '\n'
        for path in (CONTROL, CANDIDATE):
            for optimized in (False, True):
                jobs.append((path, case['name'], data, case['expected'], optimized))

    base = next(c['certificate'] for c in cases if c['name'] == 'direct_zero')
    line = json.dumps(base, separators=(',', ':'))
    # These cases establish the exact change in the external framing contract.
    framing = [
        ('whitespace_on_same_line', '  ' + line + '  \n', True, True),
        ('pretty_multiline_json', json.dumps(base, indent=2) + '\n', True, False),
        ('opaque_later_line', line + '\nnot another proof\n', False, True),
        ('empty_first_line', '\n' + line + '\n', True, False),
        ('trailing_garbage_on_first_line', line + ' garbage\n', False, False),
        ('truncated_json', line[:-1] + '\n', False, False),
        ('no_final_linefeed', line, True, True),
    ]
    for name, data, old, new in framing:
        for path, expected in ((CONTROL, old), (CANDIDATE, new)):
            for optimized in (False, True):
                jobs.append((path, name, data, expected, optimized))
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(run, jobs))
    failures = [r for r in results if not r['pass']]
    receipt = {'inherited_cases': len(cases),
               'positive_inherited_cases': sum(c['expected'] for c in cases),
               'framing_cases': len(framing),
               'process_executions': len(results), 'failures': failures,
               'results': results,
               'limits': ['Canonical completeness, not every padding alias.',
                          'No proof-assistant verification of Python semantics.',
                          'The input is one physical JSON line; suffix lines are ignored.']}
    (ROOT / 'evidence/sorted_verification.json').write_text(
        json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
