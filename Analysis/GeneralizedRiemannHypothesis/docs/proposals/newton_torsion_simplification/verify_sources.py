#!/usr/bin/env python3
"""Verify pinned Git object identities; requires a local ProveIt checkout."""
import csv, subprocess, sys
from pathlib import Path
COMMIT='ef7d441dcb37ea944b7ac15731bb766f2e1354ea'
if len(sys.argv)!=2:
    sys.exit('usage: python3 verify_sources.py /path/to/ProveIt')
repo=sys.argv[1]
def git(*args):
    return subprocess.check_output(['git','-C',repo,*args],text=True).strip()
with (Path(__file__).parent/'source_manifest.tsv').open() as f:
    rows=list(csv.DictReader(f,delimiter='\t'))
for row in rows:
    rev=f'{COMMIT}:{row["path"]}'
    actual=git('rev-parse',rev)
    assert actual==row['sha'],(row['path'],actual,row['sha'])
    assert git('cat-file','-t',actual)==row['kind']
print(f'Verified {len(rows)} pinned objects at {COMMIT}.')
