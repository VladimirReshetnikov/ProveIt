#!/usr/bin/env python3
"""Verify delivered bytes and recorded component evidence; does not run proof kernels."""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(condition, message):
    if not condition:
        raise SystemExit(message)

def inside(relative):
    p = (ROOT / relative).resolve()
    require(p.is_relative_to(ROOT), "Unsafe manifest path: " + relative)
    return p

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, help='Optionally bind the measured sources to a matching checkout')
    args = ap.parse_args()
    manifest = json.loads((ROOT/'MANIFEST.json').read_text())
    for row in manifest['files']:
        p = inside(row['path'])
        require(p.is_file(), 'Missing: '+row['path'])
        require(p.stat().st_size == row['bytes'] and sha(p) == row['sha256'],
                'Changed: '+row['path'])

    lr = json.loads((ROOT/'lean-normalization/evidence/result.json').read_text())
    require(lr['status'] == 'PASS' and lr['same_api_output'], 'Lean replay not accepted')
    require(not lr['full_endpoint_rebuilt'], 'Unexpected Lean scope marker')
    for row in lr['records']:
        log = ROOT/'lean-normalization/evidence'/row['log']
        require(row['returncode'] == 0 and sha(log) == row['log_sha256'],
                'Lean log mismatch: '+row['name'])

    rr = json.loads((ROOT/'rocq/evidence/final/result.json').read_text())
    require(rr['complete'] and rr['recursive_audit'] == 'passed', 'Rocq component audit incomplete')
    for row in rr['sources']:
        require(sha(ROOT/'rocq'/row['delivered']) == row['delivered_sha256'],
                'Rocq delivered source mismatch: '+row['delivered'])
    for row in rr['checks']:
        log = ROOT/'rocq/evidence/final/logs'/(row['name'].replace('/','_')+'.log')
        require(row['exit_code'] == 0 and sha(log) == row['log_sha256'],
                'Rocq log mismatch: '+row['name'])

    census = json.loads((ROOT/'evidence/architecture_metrics.json').read_text())
    require(census['status'] == 'COMPLETE_SOURCE_CENSUS', 'Incomplete census')
    require(not census['unresolved_imports'], 'Unresolved current-source imports')
    require(len(census['sources']) == census['totals']['module_count'], 'Census count mismatch')
    require(sum(x['bytes'] for x in census['sources']) == census['totals']['source_bytes'],
            'Census byte mismatch')
    if args.repo:
        repo = args.repo.resolve()
        for row in census['sources']:
            p = (repo/row['path']).resolve()
            require(p.is_relative_to(repo) and p.is_file() and sha(p) == row['sha256'],
                    'Checkout source differs: '+row['path'])
    print('PASS: delivered bytes and recorded evidence match.')
    print('This verifies records and source bindings, not fresh proof checking.')
    print('Use rocq/build.py and lean-normalization/reproduce.py for fresh component proofs.')

if __name__ == '__main__':
    main()
