#!/usr/bin/env python3
"""Check selected recorded object IDs in a local repository. No network access."""
import csv, subprocess, sys
from pathlib import Path
root=Path(__file__).resolve().parent
if len(sys.argv)!=2: raise SystemExit('usage: verify_sources.py /path/to/ProveIt')
repo=sys.argv[1]; prefix='Analysis/GeneralizedRiemannHypothesis/'
rev='a96fd3f7b682add165f649414b90e243bc18b101'
def git(*a): return subprocess.check_output(['git','-C',repo,*a],text=True).strip()
with (root/'source_audit.tsv').open() as f:
    for row in csv.DictReader(f,delimiter='\t'):
        sha=row['git_blob_sha1']; path=row['path']
        if 'rechecked' in row['status']:
            actual=git('rev-parse',rev+':'+prefix+path)
            assert actual==sha,(path,actual,sha)
        else:
            assert git('cat-file','-t',sha)=='blob',(path,sha)
        print('source OK',path,sha)
ptree='7fd24ac9ab5506bf6d0d21fd52034010a4f72243'
assert git('cat-file','-t',ptree)=='tree'
with (root/'proposal_audit.tsv').open() as f:
    for row in csv.DictReader(f,delimiter='\t'):
        actual=git('rev-parse',ptree+':'+row['folder'])
        assert actual==row['observed_tree_sha1'],(row['folder'],actual)
        print('proposal tree OK',row['folder'],actual)
