#!/usr/bin/env python3
"""Run all new component checks normally and with optimization, comparing outputs.

Standard library only. The asymptotic and upstream-algebra dependencies are
mathematical claims documented in report.pdf, not consequences of these tests.
"""
from pathlib import Path
import hashlib
import json
import platform
import subprocess
import sys


def main():
    root = Path(__file__).resolve().parent
    output = root / 'results'
    output.mkdir(exist_ok=True)
    specifications = [
        ('packing', 'verify_packing.py', 'packing_checks.json'),
        ('annulus', 'annulus_modes.py', 'annulus_checks.json'),
        ('schedule', 'verify_schedule.py', 'schedule_results.json'),
    ]
    records = []
    for name, script_name, result_name in specifications:
        result_path = output / result_name
        saved = {}
        for mode, flags in [('normal', []), ('optimized', ['-O'])]:
            command = [sys.executable, *flags, '-B', str(root / 'code' / script_name)]
            completed = subprocess.run(command, cwd=root, text=True,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            if completed.returncode:
                raise RuntimeError(f'{name} ({mode}) failed:\n'
                                   + completed.stdout[-4000:] + completed.stderr[-4000:])
            if not result_path.is_file():
                raise RuntimeError(f'{name} did not produce its result file')
            raw = result_path.read_bytes()
            report = json.loads(raw)
            if report.get('status') not in ('PASS', 'all exact controls passed'):
                raise RuntimeError(f'{name} reported an unsuccessful status')
            saved[mode] = raw
            archive_path = output / (result_path.stem + '_' + mode + '.json')
            archive_path.write_bytes(raw)
        if saved['normal'] != saved['optimized']:
            raise RuntimeError(f'{name}: normal and optimized result bytes differ')
        digest = hashlib.sha256(saved['normal']).hexdigest()
        records.append({'component': name, 'status': 'PASS',
                        'normal_optimized_byte_identical': True,
                        'result_sha256': digest,
                        'result': 'results/' + result_name,
                        'commands': ['python3 -B code/' + script_name,
                                     'python3 -O -B code/' + script_name]})
        if name == 'annulus':
            (output / 'annulus_execution_validation.json').write_text(
                json.dumps({'status': 'PASS', 'normal_optimized_byte_identical': True,
                            'normal_sha256': digest, 'optimized_sha256': digest,
                            'scope': 'All explicit verification gates remain active under -O.'},
                           indent=2, sort_keys=True) + '\n')
        print(name + ': PASS (normal and optimized results identical)', flush=True)
    summary = {
        'status': 'PASS',
        'python': {'implementation': platform.python_implementation(),
                   'version': platform.python_version()},
        'components': records,
        'scope': 'New finite component checks only; not a complete SAT solver, '
                 'asymptotic proof by experiments, formal proof-assistant build, '
                 'or SAT performance benchmark.',
        'scope_of_upstream_validation': 'No upstream code or proof-assistant build is run.',
    }
    (output / 'verification_summary.json').write_text(
        json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print('All component checks passed; see results/verification_summary.json.')


if __name__ == '__main__':
    main()
