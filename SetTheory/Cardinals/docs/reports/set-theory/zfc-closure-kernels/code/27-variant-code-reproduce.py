#!/usr/bin/env python3
"""Replay the selected finite results without repeating the broad searches.

Standard library only. Run with Python 3.10+ and assertions enabled.
The optional --recompile also regenerates the three frozen compiler recipes.
This does not invoke Lean or Coq or claim to decide consistency.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
import time

BASE = Path(__file__).resolve().parents[1]


def main():
    if not __debug__:
        raise SystemExit('Run without -O: inherited machine/RM checkers use assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--recompile', action='store_true')
    args = parser.parse_args()
    data = BASE / 'data'
    logs = data / 'replay_logs'
    logs.mkdir(parents=True, exist_ok=True)
    jobs = [
        ('literal_tables', 'code', 'verify_tables.py', '--output', str(data / 'table_verification.json')),
        ('ksp_inverse', 'code', 'ksp_certificate.py', '--output', str(data / 'ksp_verification.json')),
        ('public_l_basis', 'experiments/logic_certificates', 'verify_basis.py', '--mutations'),
        ('kbp_basis', 'experiments/logic_certificates', 'verify_kbp.py'),
        ('ks_countermodel', 'experiments/logic_certificates', 'verify_ks_countermodel.py'),
        ('machine_candidate', 'experiments/machine_search', 'grammar_search/verify_candidate.py'),
        ('machine_strict_symbolic', 'experiments/machine_search', 'grammar_search/strict_affine.py'),
        ('machine_independent_rm', 'experiments/machine_search', 'grammar_search/independent_rm_check.py'),
        ('compiler_frozen_certificates', 'experiments/basis_compiler', 'check_certificates.py', '--directory', 'frozen'),
    ]
    results = []

    def run(job):
        name, cwd, script, *extra = job
        command = [sys.executable, '-B', script, *extra]
        started = time.monotonic()
        proc = subprocess.run(command, cwd=BASE / cwd, text=True, capture_output=True)
        log = proc.stdout + ('\nSTDERR:\n' + proc.stderr if proc.stderr else '')
        (logs / (name + '.txt')).write_text(log)
        record = {
            'name': name,
            'cwd_relative_to_package': cwd,
            'script': script,
            'passed': proc.returncode == 0,
            'returncode': proc.returncode,
            'elapsed_seconds': round(time.monotonic() - started, 3),
            'log': str((logs / (name + '.txt')).relative_to(BASE)),
            'log_sha256': hashlib.sha256(log.encode()).hexdigest(),
        }
        results.append(record)
        print(name + ': ' + ('PASS' if proc.returncode == 0 else 'FAIL'), flush=True)
        if proc.returncode:
            print(log[-5000:], file=sys.stderr)
            save()
            raise SystemExit(proc.returncode)

    def save():
        value = {
            'scope': 'Finite certificates, universal symbolic contracts, and selected compiler reproduction; no new proof-assistant kernel build.',
            'python': sys.version.split()[0],
            'assertions_enabled': __debug__,
            'all_selected_checks_passed': all(x['passed'] for x in results),
            'selected_checks_completed': len(results),
            'new_lean_build_performed': False,
            'new_coq_build_performed': False,
            'jobs': results,
        }
        (data / 'verification_summary.json').write_text(json.dumps(value, indent=2) + '\n')

    for job in jobs:
        run(job)
    if args.recompile:
        with tempfile.TemporaryDirectory(prefix='proveit-basis-reproduction-') as tmp:
            run(('compiler_selected_reproduction', 'experiments/basis_compiler',
                 'reproduce.py', '--output', str(Path(tmp) / 'results')))
    save()
    print(f'All {len(results)} selected checks passed. See data/verification_summary.json.')


if __name__ == '__main__':
    main()
