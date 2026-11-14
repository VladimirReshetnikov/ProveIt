#!/usr/bin/env python3
"""Independent deterministic rooted labeled-TM comparison of supplied U208 releases."""
from pathlib import Path
from collections import deque
import json,hashlib,argparse
HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--inputs',type=Path,default=HERE/'inputs')
parser.add_argument('--output',type=Path,default=HERE/'table_comparison.json')
args=parser.parse_args()
def table(p):
    rows={}
    for ln in p.read_text().splitlines():
        if not ln.strip() or ln.startswith('#'): continue
        q,b,w,d,r=ln.split();k=(int(q),int(b))
        if k in rows:raise ValueError('duplicate')
        rows[k]=(int(w),d,int(r))
    states={q for q,b in rows}
    if set(rows)!={(q,b) for q in states for b in (0,1)}:raise ValueError('partial')
    targets={r for w,d,r in rows.values()};halt=targets-states
    if len(halt)!=1:raise ValueError('halt')
    return rows,states,next(iter(halt))
def canon(rows,states,halt):
    mapping={0:0};queue=deque([0]);out=[]
    while queue:
        q=queue.popleft()
        for b in (0,1):
            w,d,r=rows[q,b]
            if r==halt:n='H'
            else:
                if r not in mapping:mapping[r]=len(mapping);queue.append(r)
                n=mapping[r]
            out.append([mapping[q],b,w,d,n])
    if set(mapping)!=states:raise ValueError('unreachable graph states')
    raw=json.dumps(out,separators=(',',':')).encode()
    return hashlib.sha256(raw).hexdigest(),mapping,out
records=[];canonical={}
manifest=json.loads((args.inputs/'tables_manifest.json').read_text())
for source in manifest['tables']:
    p=args.inputs/source['file'];digest=hashlib.sha256(p.read_bytes()).hexdigest()
    if digest!=source['sha256']:raise ValueError('table input digest mismatch')
    t,states,h=table(p);key,m,out=canon(t,states,h)
    record={'archive':source['archive'],'path':source['path'],'states':len(states),'rows':len(t),'halt':h,'sha256':digest,'canonical_sha256':key,'canonical_map':m}
    records.append(record);canonical.setdefault(key,out)
summary={'snapshot':'c086b5adaa6228009365768946d691dfc49a20bb','method':'BFS from start 0, visit read-0 then read-1 edges, preserve write bit, direction, and halt','class_count':len(canonical),'tables':records,'canonical_tables':canonical}
args.output.write_text(json.dumps(summary,indent=2)+'\n')
for x in records:print(x['archive'],x['path'],x['canonical_sha256'])
print('classes',len(canonical))
