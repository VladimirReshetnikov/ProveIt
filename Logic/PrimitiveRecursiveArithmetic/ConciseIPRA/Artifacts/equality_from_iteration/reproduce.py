"""Reproduce the delivered checker measurements and finite verification."""

import csv
import json
from pathlib import Path
import platform
import subprocess
import sys


ROOT = Path(__file__).resolve().parent


def main():
    evidence = ROOT / 'evidence'
    evidence.mkdir(exist_ok=True)
    run = subprocess.run([sys.executable, str(ROOT / 'code' / 'verify.py')],
                         cwd=ROOT, capture_output=True, text=True)
    (evidence / 'verification.log').write_text(run.stdout + run.stderr)
    if run.returncode:
        print(run.stdout + run.stderr)
        raise SystemExit(run.returncode)
    results = json.loads((ROOT / 'code' / 'results.json').read_text())
    (evidence / 'verification.json').write_text(json.dumps(results, indent=2) + '\n')
    with (evidence / 'metrics.csv').open('w', newline='') as stream:
        writer = csv.writer(stream)
        writer.writerow(['module', 'tokens', 'ast_nodes', 'normalized_bytes', 'gzip9_bytes'])
        for name, metrics in results['metrics'].items():
            writer.writerow([name, metrics['tokens'], metrics['ast_nodes'],
                             metrics['normalized_bytes'], metrics['gzip9_bytes']])
    expected = {
        'raw_control.py': (959, 1026, 3039, 966),
        'raw_two_case.py': (954, 1019, 2996, 955),
        'normalized_control.py': (987, 1059, 3064, 982),
        'checker.py': (979, 1047, 3011, 965),
    }
    if platform.python_version() == '3.12.14':
        for name, values in expected.items():
            measured = results['metrics'][name]
            actual = tuple(measured[k] for k in
                           ('tokens', 'ast_nodes', 'normalized_bytes', 'gzip9_bytes'))
            if actual != values:
                raise RuntimeError(f'Measurement changed for {name}: {actual} != {values}')
    print('All checker, translation, binding, and normalization checks passed.')
    print('Standalone process checks:', results['standalone_process_checks'])
    print('Unexpected outcomes:', results['unexpected_outcomes'])
    for name, metrics in results['metrics'].items():
        print(name, metrics['tokens'], metrics['ast_nodes'],
              metrics['normalized_bytes'], metrics['gzip9_bytes'])


if __name__ == '__main__':
    main()
