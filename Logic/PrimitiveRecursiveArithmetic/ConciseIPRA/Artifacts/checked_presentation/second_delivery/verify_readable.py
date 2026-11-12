"""Compare the readable standalone checker with its strict compact source."""
from pathlib import Path
import concurrent.futures
import hashlib
import json
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PROGRAMS = ['code/checker_strict.py', 'code/readable_checker.py']


def run(task):
    program, fixture, optimized, expected = task
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    result = subprocess.run(command + [str(ROOT / program)],
                            input=(ROOT / fixture).read_bytes(),
                            capture_output=True, timeout=15)
    accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
    return {'program': program, 'fixture': fixture, 'optimized': optimized,
            'expected': expected, 'accepted': accepted,
            'passed': accepted == expected}


def main():
    tasks = []
    for group in ['proofs', 'boundary']:
        folder = ROOT / 'tests/strict' / group
        cases = json.loads((folder / 'cases.json').read_text())
        for case in cases:
            fixture = str((folder / case['file']).relative_to(ROOT))
            for program in PROGRAMS:
                for optimized in (False, True):
                    tasks.append((program, fixture, optimized, case['expected']))
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        rows = list(pool.map(run, tasks))
    report = {'python': platform.python_version(), 'executions': len(rows),
              'programs': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
                           for p in PROGRAMS},
              'failures': [r for r in rows if not r['passed']], 'results': rows,
              'scope': 'Existing strict proof and boundary fixtures only; ordinary and -O execution.'}
    (ROOT / 'evidence/readable_validation.json').write_text(
        json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
    if report['failures']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
