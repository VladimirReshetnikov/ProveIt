#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,sys
if len(sys.argv)!=2:raise SystemExit('usage: compare.py /tmp/PEER_ROOT')
p=Path(__file__).resolve().parent;r=Path(sys.argv[1]);a=json.loads((p/'author-evidence/state.json').read_text());b=json.loads((r/'state.json').read_text());h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if b['status']!='PASS' or len(a['records'])!=len(b['records']):raise SystemExit('peer is not PASS or record count differs')
for x,y in zip(a['records'],b['records']):
 for f in ('module','exit','source_sha256','object_sha256','log_sha256','dependency_hashes'):
  if x[f]!=y[f]:raise SystemExit(f'{y["module"]}: {f} differs')
 n=y['module']
 for q,f in ((r/'src/DiophantineConsistency'/(n+'.lean'),'source_sha256'),(r/'logs'/(n+'.log'),'log_sha256'),(r/'lib/DiophantineConsistency'/(n+'.olean'),'object_sha256')):
  if h(q)!=y[f]:raise SystemExit(f'{n}: {f} changed')
print('PASS: four source/object/full-log/direct-dependency rows match; prefix and package qualifications remain')
