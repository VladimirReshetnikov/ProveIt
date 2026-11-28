#!/usr/bin/env python3
"""Compare recorded blob hashes against an existing ProveIt Git checkout."""
import csv, pathlib, subprocess, sys
HERE=pathlib.Path(__file__).resolve().parent
REV='17bf37ab3b6740d5d7430065d2f2a1a2a03e8a0e'
BASE='Analysis/GeneralizedRiemannHypothesis/'
repo=pathlib.Path(sys.argv[1])
expected=[]
with open(HERE/'source_anchors.tsv') as f:
    for row in csv.DictReader(f,delimiter='\t'):
        expected.append((BASE+row['path'],row['git_blob_sha1']))
with open(HERE/'proposal_audit.tsv') as f:
    for row in csv.DictReader(f,delimiter='\t'):
        expected.append((BASE+'docs/proposals/'+row['proposal']+'/'+row['tex_file'],row['git_blob_sha1']))
fail=[]
for path,sha in expected:
    result=subprocess.run(['git','-C',str(repo),'rev-parse',REV+':'+path],capture_output=True,text=True)
    if result.returncode or result.stdout.strip()!=sha: fail.append((path,sha,result.stdout.strip()))
for item in fail: print('MISMATCH',*item)
print(f'{len(expected)-len(fail)}/{len(expected)} expected blobs match at {REV}')
raise SystemExit(bool(fail))
