#!/usr/bin/env python3
"""Portable replay entry point for the tail reconstruction certificates.

Default: verify inherited-source hashes, primary p10, independent p10,
and the COMPLETE independent p12 scan. With --full, also recompute the
optional coefficient bound and build/run the independent C++ p12 scan.
The C++ executable and freshly generated residue list use a temporary
folder, so no compiler output or binary is left in this package.
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

ROOT=Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_hashes():
    manifest=json.loads((ROOT/'provenance_inputs/manifest.json').read_text())
    for item in manifest['source_files']:
        source=ROOT/'provenance_inputs'/item['archive'].removesuffix('.zip')/item['member']
        if not source.is_file() or digest(source)!=item['sha256']:
            raise RuntimeError(f"Inherited source hash mismatch: {item['archive']}::{item['member']}")
    return len(manifest['source_files'])


def execute(args,label):
    started=time.perf_counter()
    completed=subprocess.run(args,cwd=ROOT,text=True,capture_output=True,check=False)
    if completed.returncode:
        raise RuntimeError(f'{label} failed with exit {completed.returncode}:\n'
                           f'{completed.stdout}\n{completed.stderr}')
    print(f'PASS: {label}',flush=True)
    return {'check':label,'exit_code':completed.returncode,
            'elapsed_seconds_diagnostic':round(time.perf_counter()-started,3)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full',action='store_true',help='also replay the factor-product bound and independent C++ scan')
    args=parser.parse_args()
    original_residue_hash=digest(ROOT/'complete_p12.json')
    recorded_p10=json.loads((ROOT/'complete_p10.json').read_text())
    recorded_independent_p10=json.loads((ROOT/'verify_p10_independent.json').read_text())
    checked_sources=source_hashes()
    checks=[]
    for name,label in [('complete_p10.py','primary exact order-ten certificate'),
                       ('verify_p10_independent.py','independent order-ten Padé/Bernoulli certificate'),
                       ('replay_p12_independent.py','all 11,513 order-twelve cases by independent Python algorithms')]:
        checks.append(execute([sys.executable,'-B',str(ROOT/name)],label))
    if json.loads((ROOT/'complete_p10.json').read_text())!=recorded_p10:
        raise RuntimeError('Primary order-ten recorded mathematical result changed')
    if json.loads((ROOT/'verify_p10_independent.json').read_text())!=recorded_independent_p10:
        raise RuntimeError('Independent order-ten recorded mathematical result changed')
    if args.full:
        checks.append(execute([sys.executable,'-B',str(ROOT/'coefficient_norm_bound.py'),'6'],
                              'optional sharper coefficient-norm threshold'))
        compiler=next((shutil.which(name) for name in ('c++','g++','clang++') if shutil.which(name)),None)
        if compiler is None:raise RuntimeError('--full requires a C++17 compiler (c++, g++, or clang++)')
        with tempfile.TemporaryDirectory(prefix='proveit-tail-checks-') as temporary:
            temporary=Path(temporary)
            binary=temporary/('complete_p12.exe' if os.name=='nt' else 'complete_p12')
            output=temporary/'complete_p12.json'
            checks.append(execute([compiler,'-O2','-std=c++17',str(ROOT/'complete_p12.cpp'),'-o',str(binary)],
                                  'build independent C++ order-twelve verifier'))
            checks.append(execute([str(binary),str(output)],
                                  'all 11,513 order-twelve cases by independent C++ algorithms'))
            if json.loads(output.read_text())!=json.loads((ROOT/'complete_p12.json').read_text()):
                raise RuntimeError('Fresh C++ certificate differs from the complete published certificate')
    if digest(ROOT/'complete_p12.json')!=original_residue_hash:
        raise RuntimeError('Published order-twelve residue list was modified')
    report={'all_checks_passed':True,'full_replay':args.full,
            'repository_commit':'da2792fc9cc8ef19c6a314be6c65e1437fbdc66b',
            'inherited_source_hashes_verified':checked_sources,
            'order_ten_recorded_results_preserved':True,
            'order_twelve_complete_residue_list_preserved':True,
            'order_twelve_residue_file_sha256':original_residue_hash,
            'order_twelve_case_count':11513,'checks':checks}
    receipt='run_tail_checks_full.json' if args.full else 'run_tail_checks.json'
    (ROOT/receipt).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
