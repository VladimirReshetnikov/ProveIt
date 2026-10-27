#!/usr/bin/env python3
"""Reproduce the package's finite checks; this is not a SAT solver."""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def main():
    (ROOT / 'results').mkdir(exist_ok=True)
    suites = [
        ('high_moment', 'verify_high_moment_packing.py', True),
        ('orbit', 'verify_orbit_packing.py', False),
        ('schedule', 'verify_schedule.py', False),
    ]
    records = []
    for name, script, flag in suites:
        values = []
        for optimized in (False, True):
            suffix = '_optimized' if optimized else ''
            target = ROOT / 'results' / (name + '_validation' + suffix + '.json')
            command = [sys.executable] + (['-O'] if optimized else [])
            command += [str(ROOT / 'code' / script)]
            if flag:
                command.append('--output')
            command.append(str(target))
            run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            if run.returncode:
                raise RuntimeError(f'{script} failed:\n{run.stdout}\n{run.stderr}')
            data = json.loads(target.read_text())
            if data.get('status') not in ('passed', 'PASS', 'pass'):
                raise RuntimeError(f'{script} did not report a passing status')
            values.append(data)
        if values[0] != values[1]:
            raise RuntimeError(f'{script} differs between normal and optimized Python')
        records.append({'suite': name, 'status': 'passed',
                        'normal_optimized_results_identical': True})
    summary = {'status': 'passed', 'suites': records,
               'scope': 'Finite exact primitive and parameter checks, not a full '
                        'SAT solver, asymptotic proof certificate, or benchmark.'}
    (ROOT / 'results' / 'replay_summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(summary, indent=2))

if __name__ == '__main__':
    main()
