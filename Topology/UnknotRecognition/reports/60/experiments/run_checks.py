#!/usr/bin/env python3
"""Run delivered suites with complete output capture and separate result files."""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--normal-audit', action='store_true')
    parser.add_argument('--output-dir', type=Path, default=Path('results/reproduced'))
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env['PYTHONPATH'] = str(root / 'code/fast') + os.pathsep + env.get('PYTHONPATH', '')
    jobs = [
        ('maintained', [sys.executable, '-m', 'unittest', 'discover', '-s', 'tests', '-v'], root / 'code/fast', True),
        ('persistent', [sys.executable, '-m', 'unittest', 'discover', '-s', 'experiments', '-p', 'test_persistent_elimination.py', '-v'], root, True),
    ]
    if args.normal_audit:
        jobs.append(('normal_audit', [sys.executable, str(root / 'experiments/audit_normal_inventory.py'),
            '--fast', str(root / 'code/fast'), '--cases', '1000', '--output', str(output / 'normal_inventory_audit.json')], root, False))
    summary = []
    for name, command, cwd, require_summary in jobs:
        print('Running', name, flush=True)
        started = time.perf_counter()
        proc = subprocess.run(command, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        text = proc.stdout.decode(errors='replace')
        (output / (name + '.log')).write_bytes(proc.stdout)
        found = re.search(r'^Ran (\d+) tests in ([0-9.]+)s$', text, re.M)
        passed = proc.returncode == 0 and (not require_summary or bool(found and re.search(r'^OK(?:\s|$)', text, re.M)))
        record = dict(name=name, command=command, cwd=str(cwd), returncode=proc.returncode,
                      elapsed_seconds=time.perf_counter()-started, complete=passed,
                      tests=int(found.group(1)) if found else None,
                      captured_utc=datetime.now(timezone.utc).isoformat())
        summary.append(record)
        (output / 'check_summary.json').write_text(json.dumps(summary, indent=2) + '\n')
        print(json.dumps(record), flush=True)
        if not passed:
            raise SystemExit('Incomplete or failing check; see captured log')


if __name__ == '__main__':
    main()
