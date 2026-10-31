#!/usr/bin/env python3
"""Compare a finished independent replay with the frozen author outputs."""
import hashlib, json, sys
from pathlib import Path
if len(sys.argv) != 2:
    raise SystemExit('usage: compare.py /tmp/PEER_ROOT')
packet = Path(__file__).resolve().parent
peer = Path(sys.argv[1]).resolve()
author = json.loads((packet / 'author-evidence/state.json').read_text())
other = json.loads((peer / 'state.json').read_text())
if other.get('status') != 'PASS':
    raise SystemExit('peer is not PASS')
if author['order'] != other['order'] or author['allorder'] != other['allorder']:
    raise SystemExit('module graph differs')
if author['initial_source_sha256'] != other['initial_source_sha256']:
    raise SystemExit('source graph differs')
a = {r['module']: r for r in author['records']}
b = {r['module']: r for r in other['records']}
if a.keys() != b.keys():
    raise SystemExit('compiled module set differs')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for n, row in b.items():
    for field in ('exit','source_sha256','object_sha256','log_sha256'):
        if row[field] != a[n][field]:
            raise SystemExit(f'{n}: {field} differs')
    for p,field in ((peer/'lib/DiophantineConsistency'/(n+'.olean'),'object_sha256'),
                    (peer/'logs'/(n+'.log'),'log_sha256'),
                    (peer/'logs'/(n+'.lean'),'source_sha256')):
        if sha(p) != row[field]:
            raise SystemExit(f'{n}: peer {field} changed')
print(f'PASS: {len(b)} source/object/full-log rows and {len(other["allorder"])} source-graph hashes match; inherited provider scope remains.')
