#!/usr/bin/env python3
"""Replay the finite certificates; --full also runs numerical diagnostics."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--full', action='store_true',
                        help='Also repeat the higher-precision numerical diagnostics.')
    args = parser.parse_args()
    commands = [
        ['verification/conjecture_audit/verify_differential_exact.py'],
        ['verification/conjecture_audit/verify_adjacent_tail_prefix.py'],
        ['verification/digamma_continuation/compute_appell.py'],
        ['verification/digamma_continuation/mzv_weight6.py'],
        ['verification/digamma_continuation/verify_appell.py'],
    ]
    if args.full:
        commands += [
            ['verification/verify_differential_numeric.py'],
            ['verification/digamma_continuation/numeric_appell.py'],
            ['verification/lerch_continuation/verify_lerch_lattice_jets.py'],
        ]
    else:
        # Run only the exact portion; preserve the complete numerical receipt.
        commands += [['-c',
            "import importlib.util,json,pathlib;"
            "p=pathlib.Path('verification/lerch_continuation/verify_lerch_lattice_jets.py');"
            "s=importlib.util.spec_from_file_location('lerch_checks',p);"
            "m=importlib.util.module_from_spec(s);s.loader.exec_module(m);"
            "print(json.dumps(m.exact_checks(),indent=2))"]]
    records = []
    for arguments in commands:
        description = arguments[0] if arguments[0] != '-c' else 'Lerch exact checks'
        print('Running ' + description, flush=True)
        started = time.time()
        completed = subprocess.run([sys.executable] + arguments, cwd=ROOT,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True)
        record = {'task': description, 'returncode': completed.returncode,
                  'seconds': round(time.time() - started, 3),
                  'stdout': completed.stdout}
        records.append(record)
        if completed.returncode:
            print(completed.stdout)
            break
        print(f'Passed in {record["seconds"]} seconds.', flush=True)
    success = len(records) == len(commands) and all(r['returncode'] == 0 for r in records)
    target = ROOT / 'results' / ('replay_full.json' if args.full else 'replay_exact.json')
    target.write_text(json.dumps({'passed': success, 'full': args.full,
                                  'records': records}, indent=2) + '\n')
    if not success:
        raise SystemExit(1)
    print('All requested suites passed. Receipt: ' + str(target.relative_to(ROOT)))


if __name__ == '__main__':
    main()
