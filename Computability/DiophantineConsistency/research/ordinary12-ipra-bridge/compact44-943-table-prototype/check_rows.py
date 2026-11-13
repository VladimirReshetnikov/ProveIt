#!/usr/bin/env python3
"""Fail-closed exact ordered-row comparison against the retained JSON."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
JSON=ROOT/'con-zfc-diophantine-forms/36-small-tuple/coefficients/wang943_tiles.json'
JSON_SHA='66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=HERE/'Compact943Data.lean');args=ap.parse_args()
    if H(JSON)!=JSON_SHA:raise ValueError('original JSON hash mismatch')
    rows=json.loads(JSON.read_text())
    if not isinstance(rows,list) or len(rows)!=943 or any(not isinstance(r,list) or len(r)!=4 or any(type(x) is not int or x<0 for x in r) for r in rows):
        raise ValueError('invalid JSON row shape')
    source=args.source.read_text(encoding='utf-8')
    begin='-- BEGIN PINNED ORDERED ROWS\n';end='\n-- END PINNED ORDERED ROWS'
    if source.count(begin)!=1 or source.count(end)!=1:raise ValueError('row markers not unique')
    body=source.split(begin,1)[1].split(end,1)[0]
    lines=body.splitlines()
    if len(lines)!=943:raise ValueError(('wrong row count',len(lines)))
    seen=[]
    for i,line in enumerate(lines):
        m=re.fullmatch(r'  \((0|[1-9][0-9]*), (0|[1-9][0-9]*), (0|[1-9][0-9]*), (0|[1-9][0-9]*)\)(,?)',line)
        if not m or m.group(5)!=(',' if i<942 else ''):raise ValueError(('invalid row syntax',i))
        seen.append([int(m.group(j)) for j in range(1,5)])
    if seen!=rows:
        i=next(i for i,(a,b) in enumerate(zip(seen,rows)) if a!=b)
        raise ValueError(('ordered row mismatch',i,seen[i],rows[i]))
    print('PASS_EXACT_ORDERED_943_ROWS',JSON_SHA,H(args.source))
if __name__=='__main__':main()
