#!/usr/bin/env python3
"""Verify the pinned source manifest against a local ProveIt Git checkout."""
import csv, pathlib, subprocess, sys
COMMIT='cdecfeba5d834fbf2f97de71cc7766b58ec4520e'
ROOT='Analysis/GeneralizedRiemannHypothesis/'
if len(sys.argv)!=2: raise SystemExit('Usage: python verify_sources.py /path/to/ProveIt')
repo=sys.argv[1]
def git(*args):
    return subprocess.check_output(['git','-C',repo,*args],text=True).strip()
with pathlib.Path(__file__).with_name('source_manifest.tsv').open() as f:
    rows=list(csv.DictReader(f,delimiter='\t'))
for r in rows:
    obj=COMMIT+':'+ROOT+r['path']
    actual=git('rev-parse',obj)
    assert actual==r['sha'],(r['path'],actual,r['sha'])
    assert git('cat-file','-t',actual)==r['kind']
print(f'Verified {len(rows)} pinned objects at {COMMIT}.')
