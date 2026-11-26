#!/usr/bin/env python3
"""Check upstream Git object identities in a separately obtained checkout.
Does not build Lean or validate the mathematical arguments.
"""
import csv, hashlib, subprocess, sys
from pathlib import Path
COMMIT='72fead102f663d5c7a407964a13dc0cf9d977207'
root=Path(sys.argv[1]); rows=list(csv.DictReader((Path(__file__).parent/'source_map.tsv').open(),delimiter='\t'))
for row in rows:
    data=subprocess.check_output(['git','-C',str(root),'show',COMMIT+':'+row['path']])
    h=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    assert h==row['git_blob_sha1'],(row['path'],h,row['git_blob_sha1'])
    print(h,row['path'])
print(f'{len(rows)} blob identities verified; no Lean check performed.')
