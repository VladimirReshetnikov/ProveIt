#!/usr/bin/env python3
"""Replay the exact local checks; optional design files remain experimental.
Run in a prepared ProveIt checkout with its pinned Lean/Mathlib dependencies.
This script checks patch applicability; it never applies the patches.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys

packet = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('repository', type=Path, help='A prepared ProveIt checkout')
p.add_argument('--patches-only', action='store_true', help='Check source identities and patch applicability, without Lean')
p.add_argument('--proposals', action='store_true', help='Also attempt the three unvalidated design prototypes; build their production imports first')
a = p.parse_args()
repo = a.repository.resolve()

expected = json.loads((packet/'validation/source-sha256.json').read_text())
for rel, digest in expected.items():
    file = repo/rel
    if not file.is_file() or hashlib.sha256(file.read_bytes()).hexdigest() != digest:
        sys.exit(f'Source identity differs: {rel}. Use the documented source pin or audit the difference.')
print('Selected source identities match.', flush=True)

def run(args):
    print('+ ' + ' '.join(map(str,args)), flush=True)
    subprocess.run(list(map(str,args)), cwd=repo, check=True)

run(['git','apply','--check',packet/'patches/helical-period.patch',packet/'patches/pell-fixed-index.patch'])
if a.patches_only:
    sys.exit(0)

manifest = json.loads((repo/'lake-manifest.json').read_text())
mathlib = next(x for x in manifest['packages'] if x['name'] == 'mathlib')
if mathlib['rev'] != '81a5d257c8e410db227a6665ed08f64fea08e997':
    sys.exit('Mathlib revision differs from the documented pin.')
version = subprocess.check_output(['lake','env','lean','--version'],cwd=repo,text=True)
print(version.strip(), flush=True)
if 'version 4.32.0' not in version:
    sys.exit('Lean version differs from 4.32.0.')

files = ['lean/checked/HelicalPeriod.lean','lean/checked/PellAnchorSmall.lean']
if a.proposals:
    files += ['lean/proposals/SignalMomentsCore.lean','lean/proposals/CanonicalOperatingRow.lean','lean/proposals/EdgeRecognition.lean']
for rel in files:
    run(['lake','env','lean','-j1','--root='+str(packet),packet/rel])
print('Requested checks completed. This is not a full project build.', flush=True)
