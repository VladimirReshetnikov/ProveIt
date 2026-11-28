#!/usr/bin/env python3
"""Verify recorded Git object IDs against a local clone; no network required."""
import csv
import subprocess
import sys
from pathlib import Path

REV = '835c3695d07c0f77060c5cc63f92eeb52a7d21c2'
base = Path(__file__).resolve().parent
if len(sys.argv) != 2:
    raise SystemExit('usage: python3 verify_sources.py /path/to/ProveIt')
repo = sys.argv[1]
errors = 0
for name in ('source_audit.tsv', 'proposal_audit.tsv'):
    with (base/name).open(encoding='utf-8', newline='') as stream:
        for row in csv.DictReader(stream, delimiter='\t'):
            result = subprocess.run(['git','-C',repo,'rev-parse','--verify',f'{REV}:{row["path"]}'], capture_output=True, text=True)
            actual = result.stdout.strip()
            ok = result.returncode == 0 and actual == row['git_oid']
            print(('OK ' if ok else 'FAIL ') + row['path'])
            if not ok:
                print('  expected:',row['git_oid'],'actual:',actual or result.stderr.strip())
                errors += 1
raise SystemExit(1 if errors else 0)
