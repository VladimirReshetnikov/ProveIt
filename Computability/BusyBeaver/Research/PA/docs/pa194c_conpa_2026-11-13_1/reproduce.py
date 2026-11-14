#!/usr/bin/env python3
"""Rebuild PA194C and run the complete deterministic acceptance checks.

Python 3.10+ and the standard library suffice. Optional heuristic searches
and the whole-corpus census are deliberately separate. This is executable
support for the mathematical proof, not a Lean/Rocq proof kernel.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Assertions must be enabled; do not use Python -O.')
    output = ROOT / 'verification'
    logs = output / 'logs'
    logs.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    stages = [
        ('construction', ['construction/build194c.py']),
        ('independent_physical', ['independent/verify194c.py']),
        ('command_algebra', ['independent/check_commands194c.py']),
        ('corpus_novelty', ['comparison/verify_novelty.py',
                           'construction/tables/pa194c.tm', '--out',
                           'verification/novelty_replay.json']),
    ]
    completed = []
    for name, arguments in stages:
        print('Checking ' + name.replace('_', ' ') + ' ...', flush=True)
        result = subprocess.run([sys.executable, '-B'] + arguments,
                                cwd=ROOT, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (logs / (name + '.log')).write_text(result.stdout)
        if result.returncode:
            print(result.stdout[-16000:])
            raise RuntimeError(f'{name} failed with exit code {result.returncode}')
        completed.append(name)
        print('PASS: ' + name, flush=True)
    table = ROOT / 'construction/tables/pa194c.tm'
    expected = 'd759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b'
    actual = hashlib.sha256(table.read_bytes()).hexdigest()
    if actual != expected:
        raise RuntimeError('Definitive table identity changed.')
    receipt = {
        'status': 'PASS', 'family': 'PA194C', 'working_states': 194,
        'transition_rows': 388, 'source_sites': 3649,
        'universal_source_outcomes': 4749, 'startup_literal_steps': 57922,
        'command_symbolic_cases': 188, 'table_sha256': actual,
        'completed_stages': completed, 'new_end_to_end_kernel_theorem': False,
        'scope': 'Deterministic construction, complete symbolic physical audits, '
                 'symbolic command identities, and exact corpus graph novelty. '
                 'The PA calibration is the accompanying mathematical proof.'
    }
    (output / 'reproduction.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
