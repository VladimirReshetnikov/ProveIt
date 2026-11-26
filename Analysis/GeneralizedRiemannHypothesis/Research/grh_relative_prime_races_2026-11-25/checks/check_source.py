#!/usr/bin/env python3
"""Validate source-audit.tsv against a separately obtained upstream git checkout."""
import csv
import subprocess
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
REV='72fead102f663d5c7a407964a13dc0cf9d977207'
if len(sys.argv)!=2:
    raise SystemExit('usage: python checks/check_source.py /path/to/grh-lean')
repo=sys.argv[1]
with (ROOT/'source-audit.tsv').open() as fp:
    for row in csv.DictReader(fp,delimiter='\t'):
        got=subprocess.check_output(['git','-C',repo,'rev-parse',REV+':'+row['path']],text=True).strip()
        assert got==row['blob_sha'],(row['path'],got,row['blob_sha'])
        print('OK',row['path'],got)
print('All listed blob IDs verified; this is not a proof replay.')
