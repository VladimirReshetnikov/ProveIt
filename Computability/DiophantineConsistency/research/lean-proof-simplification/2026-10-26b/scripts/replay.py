#!/usr/bin/env python3
"""Replay the checked proposal files; does not apply the repository patch.

Usage: python3 scripts/replay.py /path/to/ProveIt [--core-only]
The repository's pinned Lean 4.32.0 must be available through lake/lean.
This script refuses to replay against a different commit. Output is written
under replay-results/, leaving the packaged evidence unchanged.
"""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess
import time

SNAPSHOT = '60e9c5d620c6c387d932876cfa2d9376f64ea56c'
HERE = Path(__file__).resolve().parent.parent
ap = argparse.ArgumentParser()
ap.add_argument('repository', type=Path)
ap.add_argument('--core-only', action='store_true')
args = ap.parse_args()
repo = args.repository.resolve()
actual = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
if actual != SNAPSHOT:
    raise SystemExit(f'Expected snapshot {SNAPSHOT}; found {actual}.')
if subprocess.run(['git','-C',str(repo),'diff','--quiet','HEAD']).returncode:
    raise SystemExit('Tracked source differs from the pinned commit. Use a clean checkout for this replay.')
out = HERE/'replay-results'; out.mkdir(exist_ok=True)
records = []


def run(name, command, cwd=repo, audit=False):
    start = time.monotonic()
    result = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (out/(name+'.log')).write_text(result.stdout)
    record = {'name':name, 'command':command, 'exit_code':result.returncode,
              'elapsed_seconds':round(time.monotonic()-start,3)}
    records.append(record)
    (out/'replay.json').write_text(json.dumps(records,indent=2)+'\n')
    print(f'{name}: exit {result.returncode}',flush=True)
    if result.returncode:
        raise SystemExit(f'Stopped; see {out/(name+".log")}')
    if audit:
        allowed = {'propext','Classical.choice','Quot.sound'}
        groups = re.findall(r'depends on axioms:\s*\[([^\]]*)\]',result.stdout,re.S)
        if not groups and 'does not depend on any axioms' not in result.stdout:
            raise SystemExit(f'No axiom audit output in {name}.')
        found = {x.strip() for group in groups for x in group.split(',') if x.strip()}
        if found - allowed:
            raise SystemExit(f'Unexpected axioms in {name}: {sorted(found-allowed)}')
    return result.stdout


version = run('lean-version', ['lake','env','lean','--version'])
if 'version 4.32.0,' not in version:
    raise SystemExit('Expected Lean 4.32.0.')
run('patch-applies', ['git','apply','--check',str(HERE/'patches/lookup-api.patch')])

for name in ['LookupAPI','ValidatedFold','NativeRefactorCore']:
    run(name,['lake','env','lean',str(HERE/'lean'/(name+'.lean'))],audit=True)

if not args.core_only:
    run('focused-import-build', ['lake','build',
        'DiophantineConsistency.Representation',
        'DiophantineConsistency.ArithmeticDAGPowers',
        'DiophantineConsistency.SplitCircuit59'])
    run('WitnessLayout',['lake','env','lean',str(HERE/'lean/WitnessLayout.lean')],audit=True)
    run('SplitPowerCertificate',['lake','env','lean',str(HERE/'lean/SplitPowerCertificate.lean')],audit=True)
    run('gap-fixture-bytes',['python3',str(HERE/'scripts/check_gap_fixture.py'),str(repo)])
    run('GapExactDataFixture',['lake','env','lean',str(HERE/'lean/GapExactDataFixture.lean')],audit=True)

print('All selected checks passed. No repository patch was applied.')
