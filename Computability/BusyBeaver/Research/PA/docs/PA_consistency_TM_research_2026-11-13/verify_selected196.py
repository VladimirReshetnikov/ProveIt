#!/usr/bin/env python3
"""Offline check of the exported fourteen-table rooted graph census."""
from pathlib import Path
import hashlib,json
from build_196_census import parse,canonical

ROOT=Path(__file__).resolve().parent/'selected196_tables'
manifest=json.loads((ROOT/'manifest.json').read_text())
digests=set()
for entry in manifest['files']:
    raw=(ROOT/entry['file']).read_bytes()
    if hashlib.sha256(raw).hexdigest()!=entry['dense_sha256']:raise ValueError('file hash differs')
    table=parse(raw)
    if set(table)!={(q,b)for q in range(196)for b in [0,1]}:raise ValueError('working rows differ')
    if {t for _,_,t in table.values()}-set(range(196))!={196}:raise ValueError('halt differs')
    rows,labels=canonical(table)
    if len(labels)!=196:raise ValueError('not all states graph-reachable')
    digest=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest()
    if digest!=entry['canonical_graph_sha256']:raise ValueError('canonical form differs')
    digests.add(digest)
if len(manifest['files'])!=14 or len(digests)!=14:raise ValueError('census differs')
print(json.dumps({'status':'CENSUS_PASS','tables':14,'rooted_action_graph_classes':14,
                  'scope':'Finite graph census only; includes two experimental MP variants.'},indent=2))
