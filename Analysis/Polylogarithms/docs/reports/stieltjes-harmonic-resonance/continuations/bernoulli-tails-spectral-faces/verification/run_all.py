#!/usr/bin/env python3
"""Run the self-contained exact certificates and/or numerical diagnostics.

Exact replay is the default. Numerical diagnostics include high-precision
quadrature and may take several minutes. No network access is needed.
"""
from pathlib import Path
import argparse
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
EXACT = [
    'allpowers/verify_allpowers.py',
    'allpowers/verify_ordinary_identity.py',
    'allpowers/verify_even_tail_extension.py',
    'allpowers/quintic_sextic.py',
    'moment/completion_certificate.py',
    'moment/verify_eventual_ten.py',
    'moment/verify_p10_dependencies.py',
    'gaps/verify_exact.py',
]
NUMERICAL = [
    'allpowers/verify_numerics.py',
    'gaps/verify_marked_gaps.py',
    'spectral/verify_faces.py',
    'spectral/verify_faces_high_precision.py',
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exact', action='store_true', help='run exact certificates')
    parser.add_argument('--numerical', action='store_true', help='run numerical diagnostics')
    args = parser.parse_args()
    groups = []
    if args.exact or not args.numerical:
        groups.append(('exact', EXACT))
    if args.numerical:
        groups.append(('numerical', NUMERICAL))
    logs = ROOT / 'logs'
    logs.mkdir(exist_ok=True)
    for group, tasks in groups:
        results = []
        for task in tasks:
            started = time.monotonic()
            print(f'Running {task}', flush=True)
            result = subprocess.run([sys.executable, str(ROOT / task)],
                cwd=(ROOT / task).parent, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT)
            log_name = task.replace('/', '__').replace('.py', '.log')
            (logs / log_name).write_text(result.stdout)
            record = {'program': task, 'exit_code': result.returncode,
                      'seconds': round(time.monotonic() - started, 3),
                      'log': 'logs/' + log_name}
            results.append(record)
            print(('PASS' if result.returncode == 0 else 'FAIL')
                  + f' {task} ({record["seconds"]} s)', flush=True)
            receipt = {'group': group, 'python': sys.version,
                       'all_passed': all(r['exit_code'] == 0 for r in results),
                       'completed_programs': len(results), 'expected_programs': len(tasks),
                       'results': results}
            (ROOT / ('REPLAY_' + group.upper() + '.json')).write_text(
                json.dumps(receipt, indent=2) + '\n')
            if result.returncode:
                print(result.stdout[-6000:])
                raise SystemExit(result.returncode)


if __name__ == '__main__':
    main()
