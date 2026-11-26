#!/usr/bin/env python3
"""Optional offline audit against a local clone; no Lean execution.
Checks tree membership directly by git ls-tree, not the current worktree.
"""
import csv, pathlib, subprocess, sys
base=pathlib.Path(__file__).resolve().parent.parent
TREE='72fead102f663d5c7a407964a13dc0cf9d977207'
if len(sys.argv)!=2:
    raise SystemExit('usage: python checks/check_source.py /path/to/grh-lean')
repo=sys.argv[1]
def git(*args): return subprocess.check_output(['git','-C',repo,*args],text=True).strip()
with (base/'source-audit.tsv').open() as f:
    for row in csv.DictReader(f,delimiter='\t'):
        line=git('ls-tree',TREE,'--',row['path'])
        if not line: raise ValueError('missing '+row['path'])
        header,path=line.split('\t',1); mode,kind,sha=header.split()
        assert path==row['path'] and kind=='blob' and sha==row['git_blob_sha'],(row,line)
        print('OK',sha,path)
print('All listed Git blob identities verified; no theorem replay performed.')
