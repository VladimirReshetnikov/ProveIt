#!/usr/bin/env python3
"""Replay finite arithmetic checks for the concrete 9/12/27 constructions.

The inherited unbounded compiler and consistency calibration are mathematical
dependencies, not established by running this program. Python standard library.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
VERIFY = ROOT / 'verification'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def bindings():
    catalog = json.loads((ROOT/'upstream/SOURCES.json').read_text())
    for row in catalog['files']:
        path = ROOT/'upstream'/row['local_path']
        require(path.is_file(), f'Missing upstream source: {row["local_path"]}')
        require(digest(path) == row['sha256'], f'Upstream source changed: {row["local_path"]}')
    signed_catalog = json.loads((ROOT/'integer27/SOURCES.json').read_text())
    for row in signed_catalog['files']:
        require(digest(ROOT/'integer27'/row['path']) == row['sha256'],
                f'Signed source changed: {row["path"]}')
    mapping = json.loads((ROOT/'COEFFICIENT_BINDINGS.json').read_text())
    for row in mapping['authenticated_files']:
        require(digest(ROOT/row['path']) == row['sha256'], f'Binding hash mismatch: {row["path"]}')
    table = ROOT/'upstream/machine/k215.tm'
    rows = []
    for line in table.read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        state, bit, written, move, target = line.split()
        rows.append([int(state),int(bit),int(written),{'L':-1,'R':1}[move],int(target)])
    exported = json.loads((ROOT/'upstream/t4/bridge/sources/k215_transitions.json').read_text())
    require(len(rows) == 430, 'Literal machine has incorrect transition count')
    require(rows == exported['transitions'], 'Literal machine and compiler transition export differ')
    require(rows[0] == [0,0,1,1,93], 'Incorrect initialized first transition')
    require(digest(ROOT/'coefficients/t4_windows.json') ==
            digest(ROOT/'upstream/t4/bridge/t4_windows.json'), 'Tile copies differ')
    return {'selected_upstream_files':len(catalog['files']),
            'signed_source_files':len(signed_catalog['files']),
            'literal_transition_rows':len(rows),
            'machine_sha256':digest(table),
            'tile_sha256':digest(ROOT/'coefficients/t4_windows.json')}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full-t4', action='store_true', help='also enumerate all filtered T4 candidates')
    args = ap.parse_args()
    VERIFY.mkdir(exist_ok=True)
    bound = bindings()
    jobs = []
    if args.full_t4:
        jobs += [('t4_enumeration', ['upstream/t4/bridge/check_t4.py']),
                 ('t4_independent', ['upstream/t4/review/independent_t4_checks.py'])]
    jobs += [
        ('base', ['code/build_base.py']),
        ('fixed_coefficients', ['code/fixed_coefficients.py']),
        ('nine_build', ['nine/nine_compressor.py','base/quartic32.upstream.json','nine/generated']),
        ('nine_checks', ['nine/check_nine.py','base/quartic32.upstream.json','nine/generated']),
        ('nine_fixed_instance', ['nine/verify_fixed_instance.py','--package-root','.',
                                '--generated','nine/generated','--output','verification/nine_fixed_instance.json']),
        ('twelve_build', ['direct12/algebra12_build.py']),
        ('twelve_checks', ['direct12/algebra12_verify.py']),
        ('integer27', ['integer27/build_integer27.py']),
    ]
    records = []
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    for name, argv in jobs:
        print(f'Running {name} ...', flush=True)
        completed = subprocess.run([sys.executable,*argv],cwd=ROOT,env=env,
                                   text=True,capture_output=True)
        log = VERIFY/(name+'.log')
        log.write_text(completed.stdout+completed.stderr)
        record = {'name':name,'command':['python3',*argv],
                  'exit_code':completed.returncode,'log':str(log.relative_to(ROOT)),
                  'log_sha256':digest(log)}
        records.append(record)
        if completed.returncode:
            print(completed.stdout+completed.stderr,file=sys.stderr)
            raise RuntimeError(f'{name} failed; see {log}')
        print(f'PASS {name}', flush=True)
    bound_after = bindings()
    require(bound == bound_after, 'Bound source data changed during replay')
    receipt = {'status':'PASS','python':platform.python_version(),
               'repository_pin':'f0ae4e0991ca44a7bb4e5671d42e33d775e48035',
               'full_t4_replayed':args.full_t4,'source_bindings':bound,
               'jobs':records,
               'scope':'Finite source, polynomial, degree, circuit, coefficient and modular checks. No consistency decision or new proof-assistant endpoint.'}
    (VERIFY/'REPRODUCE.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'PASS','jobs':len(records),'full_t4':args.full_t4,
                      'receipt':'verification/REPRODUCE.json'},indent=2))


if __name__ == '__main__':
    main()
