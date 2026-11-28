#!/usr/bin/env python3
"""Check pinned blob identities against an existing Git checkout."""
import csv, pathlib, subprocess, sys
commit='ef7d441dcb37ea944b7ac15731bb766f2e1354ea'
repo=pathlib.Path(sys.argv[1]).resolve()
root=pathlib.Path(__file__).resolve().parent
count=0
for table in ['source_anchors.tsv','proposal_audit.tsv']:
    with (root/table).open() as f:
        for row in csv.DictReader(f, delimiter='\t'):
            path=row['path']
            actual=subprocess.check_output(['git','-C',str(repo),'rev-parse',f'{commit}:{path}'],text=True).strip()
            assert actual==row['blob_sha'], (path,actual,row['blob_sha'])
            count+=1
print(f'{count} pinned source and proposal blobs verified')
