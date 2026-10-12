#!/usr/bin/env python3
"""Replay the exact proof certificates and the optional numerical diagnostics.

Run from anywhere. Supplied records are never overwritten: source programs
are copied into a temporary workspace, and generated certificates are compared
with the archived originals. Logs and the final receipt go into checks/.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exact', action='store_true')
    parser.add_argument('--numeric', action='store_true')
    args = parser.parse_args()
    if not (args.exact or args.numeric):
        args.exact = True
    checks = ROOT / 'checks'
    checks.mkdir(exist_ok=True)
    records = []
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')

    with tempfile.TemporaryDirectory(prefix='proveit_higher_identities_') as td:
        work = Path(td)
        shutil.copytree(ROOT / 'code', work / 'code')

        def run(name, command, cwd):
            start = time.monotonic()
            print('Running', name, flush=True)
            completed = subprocess.run(command, cwd=cwd, env=env,
                                       text=True, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT)
            (checks / (name + '.log')).write_text(completed.stdout)
            record = {'name': name, 'exit_code': completed.returncode,
                      'seconds': round(time.monotonic() - start, 3)}
            records.append(record)
            if completed.returncode:
                print(completed.stdout[-6000:], file=sys.stderr)
                raise RuntimeError(name + ' failed')
            print('PASS', name, flush=True)

        def compare_record(relative):
            generated = work / relative
            supplied = ROOT / relative
            if generated.read_bytes() != supplied.read_bytes():
                raise AssertionError('Generated record differs: ' + relative)
            records.append({'name': 'record:' + relative, 'exact_match': True,
                            'sha256': hashlib.sha256(generated.read_bytes()).hexdigest()})

        if args.exact:
            gap = work / 'code/gap_ten'
            compiler = shutil.which('c++') or shutil.which('g++')
            if not compiler:
                raise RuntimeError('A C++17 compiler is required for the exact finite certificate.')
            executable = work / 'verify_gap_ten'
            run('compile_gap_ten', [compiler, '-O3', '-std=c++17',
                                   str(gap / 'verify_gap_ten.cpp'), '-o', str(executable)], work)
            run('gap_ten_full_certificate', [str(executable), '73728',
                                             str(gap / 'gap_ten_certificate.csv')], gap)
            compare_record('code/gap_ten/gap_ten_certificate.csv')
            run('gap_ten_independent', [sys.executable, 'verify_gap_ten_independent.py'], gap)
            compare_record('code/gap_ten/gap_ten_independent_checks.json')
            run('gap_ten_inverse_and_example', [sys.executable, 'create_gap_ten_example.py'], gap)
            compare_record('code/gap_ten/gap_ten_14_24_example.json')
            run('polygamma_contacts_exact', [sys.executable, 'verify_exact_contacts.py'],
                work / 'code/collisions')
            actual = json.loads((checks / 'polygamma_contacts_exact.log').read_text())
            expected = json.loads((ROOT / 'code/collisions/exact_contacts.json').read_text())
            if actual != expected:
                raise AssertionError('Exact contact record differs.')
            records.append({'name': 'record:exact_contacts.json', 'exact_match': True})
            run('normal_forms_exact', [sys.executable, 'normal_forms.py'], work / 'code/normal_forms')
            compare_record('code/normal_forms/normal_forms_results.json')

        if args.numeric:
            tri = work / 'code/three_clusters'
            run('three_cluster_diagnostics', [sys.executable, 'verify_three_clusters.py',
                                             '--dps', '75', '--output', 'three_cluster_checks.json'], tri)
            shutil.copyfile(tri / 'three_cluster_checks.json', checks / 'three_cluster_replay.json')
            run('polygamma_contact_diagnostics', [sys.executable, 'check_polygamma_contacts.py'],
                work / 'code/collisions')

    result = {'requested': {'exact': args.exact, 'numeric': args.numeric},
              'status': 'all requested checks passed', 'checks': records}
    name = 'reproduction' + ('_exact' if args.exact else '') + ('_numeric' if args.numeric else '') + '.json'
    (checks / name).write_text(json.dumps(result, indent=2) + '\n')
    print('All requested checks passed;', name, flush=True)


if __name__ == '__main__':
    main()
