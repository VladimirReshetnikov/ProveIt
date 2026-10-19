#!/usr/bin/env python3
"""Deterministically regenerate a packed table directly from its finite witness.
No heuristic search is needed for reproduction or verification.
"""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import json,hashlib,argparse
import build_library as B
p=argparse.ArgumentParser();p.add_argument('directory',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
m=json.loads((a.directory/'manifest.json').read_text());opts=m['build_options'];d=B.build_retained(**opts)
assert m['domains']==d['domains'];pi=m['projection'];classes=m['classes'];n=len(classes)
assert set(pi)==set(d['domains'])|set(d['ports'])
assert sorted(q for g in classes for q in g)==sorted(d['domains'])
for i,g in enumerate(classes):assert all(pi[q]==i for q in g)
assert len(set(m['ports'].values()))==len(d['ports'])
assert all(pi[q]>=n for q in d['ports'])
for q in d['protected']:assert classes[pi[q]]==[q]
rows={};cert=[]
for i,g in enumerate(classes):
 for b in (0,1):
  eligible=[q for q in g if b in d['domains'][q]];chosen=eligible[0]if eligible else g[0]
  w,move,t=d['rows'][chosen,b];rows[i,b]=(w,move,pi[t])
  for q in eligible:
   w0,m0,t0=d['rows'][q,b];assert rows[i,b]==(w0,m0,pi[t0]);cert.append([q,b,i,w0,m0,pi[t0]])
r={k:m[k]for k in ('projection','classes','universal_classes','pairs','ports','entries')};r.update(table=rows,structural=cert)
out=a.output or a.directory/'rebuilt';result=B.save(d,r,out)
assert result['sha256']==m['sha256'],(result['sha256'],m['sha256'])
print(json.dumps({'status':'PASS','working_states':n,'allowed_rows_checked':len(cert),'reproduced_sha256':result['sha256']},indent=2))
