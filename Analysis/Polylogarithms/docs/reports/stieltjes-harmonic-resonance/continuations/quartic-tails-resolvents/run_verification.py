#!/usr/bin/env python3
"""Replay every mathematical verification suite from any working directory."""
from pathlib import Path
import json
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
SCRIPTS = ('verify_quartic_bridge.py', 'verify_mixed_tails.py',
           'check_moments.py', 'check_contacts.py')


def main():
    replay = ROOT / 'verification' / 'replay'
    replay.mkdir(parents=True, exist_ok=True)
    records = []
    for name in SCRIPTS:
        print(f'Running {name}', flush=True)
        start = time.perf_counter()
        logfile = replay / (Path(name).stem + '.log')
        with logfile.open('w', encoding='utf-8') as output:
            run = subprocess.run([sys.executable, str(ROOT / 'verification' / name)],
                                 cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        records.append({'script': name, 'exit_code': run.returncode,
                        'elapsed_seconds': round(time.perf_counter() - start, 3),
                        'log': str(logfile.relative_to(ROOT))})
        print(f'  exit={run.returncode}; {records[-1]["elapsed_seconds"]} s', flush=True)
        if run.returncode:
            print(logfile.read_text(encoding='utf-8')[-6000:])
            break
    summary = {'status': 'PASS' if len(records) == len(SCRIPTS)
               and all(r['exit_code'] == 0 for r in records) else 'FAIL',
               'python': platform.python_version(), 'suites': records,
               'scope': 'Exact finite symbolic checks and independent numerical diagnostics; no interval or formal-proof claim.'}
    (replay / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(summary, indent=2))
    if summary['status'] != 'PASS':
        raise SystemExit(1)


if __name__ == '__main__':
    main()

