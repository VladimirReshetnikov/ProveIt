#!/usr/bin/env python3
"""Verify pinned source blob and proposal tree hashes in a local ProveIt checkout."""
import csv, subprocess, sys
from pathlib import Path
REF='ee10f937fedac0955d28b7b860f4c44fab508204'
HERE=Path(__file__).resolve().parent
root=Path(sys.argv[1]).resolve()
for name,key in [('source_audit.tsv','git_blob_sha1'),('proposal_audit.tsv','git_tree_sha1')]:
    with (HERE/name).open(newline='') as f:
        rows=list(csv.DictReader(f,delimiter='\t'))
    for row in rows:
        actual=subprocess.check_output(['git','-C',str(root),'rev-parse',REF+':'+row['path']],text=True).strip()
        assert actual==row[key],(row['path'],actual,row[key])
    print(f'{name}: {len(rows)} objects verified at {REF}')
