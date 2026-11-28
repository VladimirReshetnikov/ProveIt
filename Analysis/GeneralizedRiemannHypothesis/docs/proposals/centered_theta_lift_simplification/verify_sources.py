#!/usr/bin/env python3
"""Check selected upstream Git blobs and declaration anchors in a local checkout."""
import argparse, csv, hashlib, re
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('root',type=Path,help='path to the upstream grh/ directory (not repository root)')
args=p.parse_args()
rows=list(csv.DictReader(Path(__file__).with_name('source_anchors.tsv').open(encoding='utf-8'),delimiter='\t'))
checked={}
for row in rows:
    path=row['path']
    if path not in checked:
        data=(args.root/path).read_bytes()
        sha=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        checked[path]=(sha,data.decode('utf-8').splitlines())
    sha, lines=checked[path]
    if sha!=row['git_blob_sha1']:
        raise SystemExit(f'{path}: expected {row["git_blob_sha1"]}, got {sha}')
    i=int(row['line'])-1
    if not re.search(r'\b(?:theorem|lemma|def)\s+'+re.escape(row['declaration'])+r'(?=\s|:|\{)',lines[i]):
        raise SystemExit(f'{path}:{i+1}: declaration mismatch: {lines[i]}')
print(f'PASS: {len(rows)} declaration anchors across {len(checked)} Git blobs')
