#!/usr/bin/env python3
"""Replay the exact production checks; no network and no third-party packages."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--optimized', action='store_true')
    ap.add_argument('--independent', action='store_true',
                    help='Also replay all independent enumerations (requires NumPy).')
    args = ap.parse_args()
    destination = ROOT / 'results' / ('replay_optimized' if args.optimized else 'replay_normal')
    destination.mkdir(parents=True, exist_ok=True)
    python = [sys.executable] + (['-O'] if args.optimized else [])
    drivers = [
        ('adaptive_rectangular.py', 'certificates.json'),
        ('schedules.py', 'schedules.json'),
        ('comparisons.py', 'comparisons.json'),
        ('check_algebra.py', 'algebra.json'),
        ('modular_rank_compilation.py', 'modular_rank_checks.json'),
    ]
    checked = []
    for script, filename in drivers:
        proc = subprocess.run(python + [str(ROOT/'code'/script), '--output', str(destination/filename)],
                              cwd=ROOT, text=True, capture_output=True)
        if proc.returncode:
            raise RuntimeError(script + '\n' + proc.stdout + '\n' + proc.stderr)
        result = json.loads((destination/filename).read_text())
        if result.get('status') != 'PASS':
            raise RuntimeError('Missing PASS status: ' + script)
        reference = json.loads((ROOT/'results'/filename).read_text())
        if result != reference:
            raise RuntimeError('Replayed result differs from delivered receipt: ' + script)
        checked.append(script)
        print(script + ': PASS (identical mathematical result)')
    if args.independent:
        for name in ('classical_r9', 'classical_r12', 'new_backend_r10', 'new_backend_r12'):
            command = python + [str(ROOT/'audit/independent/replay_menu_certificate.py'),
                '--input', str(ROOT/'audit/independent/inputs'/(name+'.json')),
                '--output', str(destination/(name+'.json'))]
            proc = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
            if proc.returncode:
                raise RuntimeError(name + '\n' + proc.stdout + '\n' + proc.stderr)
            result = json.loads((destination/(name+'.json')).read_text())
            reference = json.loads((ROOT/'audit/independent/results'/(name+'.json')).read_text())
            if result != reference:
                raise RuntimeError('Independent replay differs: '+name)
            checked.append('independent/'+name)
            print(name + ': PASS (complete independent enumeration)')
    summary = {'status':'PASS', 'optimized':args.optimized, 'checks':checked,
               'scope':'Finite certificates and compiler identities, not a complete SAT solver.'}
    (destination/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
