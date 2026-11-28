#!/usr/bin/env python3
"""Check pinned file bytes and nearby source anchors in a local ProveIt checkout."""
import csv, hashlib, sys
from pathlib import Path
if len(sys.argv)!=2:
    sys.exit('Usage: python3 verify_sources.py /path/to/ProveIt')
root=Path(sys.argv[1]); here=Path(__file__).resolve().parent
cache={}; errors=[]; anchors=0
for table in ['source_anchors.tsv','proposal_audit.tsv']:
    with (here/table).open(encoding='utf-8',newline='') as f:
        for r in csv.DictReader(f,delimiter='\t'):
            p=r['path']
            if p not in cache:
                try:
                    data=(root/p).read_bytes()
                except OSError as e:
                    errors.append(str(e)); cache[p]=None; continue
                sha=hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()
                if sha!=r['blob_sha1']: errors.append(f'{p}: expected {r["blob_sha1"]}, got {sha}')
                cache[p]=data.decode('utf-8').splitlines()
            lines=cache[p]
            line=int(r.get('line',0)); anchor=r.get('anchor','')
            if lines is not None and line and anchor:
                anchors+=1
                if not any(anchor in s for s in lines[max(0,line-4):line+3]):
                    errors.append(f'{p}:{line}: anchor {anchor!r} not found within 3 lines')
for err in errors: print('FAIL:',err)
print(f'{len(cache)} distinct files, {anchors} declaration anchors; {len(errors)} errors')
sys.exit(bool(errors))
