#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,sys
if len(sys.argv)!=2:raise SystemExit('usage: compare.py /tmp/PEER_ROOT')
p=Path(__file__).resolve().parent;root=Path(sys.argv[1]);a=json.loads((p/'author-evidence/state.json').read_text());b=json.loads((root/'state.json').read_text())
if b['status']!='PASS':raise SystemExit('peer is not PASS')
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if len(a['records'])!=len(b['records']):raise SystemExit('record count differs')
for x,y in zip(a['records'],b['records']):
 for f in ('module','exit','source_sha256','object_sha256','log_sha256'):
  if x[f]!=y[f]:raise SystemExit(f'{y["module"]}: {f} differs')
 n=y['module']
 for path,field in ((root/'logs'/(n+'.lean'),'source_sha256'),(root/'logs'/(n+'.log'),'log_sha256'),(root/'lib/DiophantineConsistency'/(n+'.olean'),'object_sha256')):
  if h(path)!=y[field]:raise SystemExit(f'{n}: {field} changed')
print('PASS: both source/object/full-log rows match; provisional inherited parent boundary remains')
