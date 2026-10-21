#!/usr/bin/env python3
"""Emit the exact finite primitive case list used by direct_merge.cpp."""
from pathlib import Path
import argparse, hashlib, json
p=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=p/'inputs/source.sites.json');ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
S=json.loads(a.source.read_text());rows=[]
for pc,op,arg in S:
    for positive in ([0,1]if op=='CD'else[0]):
        rows.append(f'{pc} {op} {-1 if arg is None else arg} {positive}\n')
assert len(rows)==6151
data=''.join(rows).encode();a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_bytes(data)
print(json.dumps({'cases':len(rows),'sha256':hashlib.sha256(data).hexdigest()}))
