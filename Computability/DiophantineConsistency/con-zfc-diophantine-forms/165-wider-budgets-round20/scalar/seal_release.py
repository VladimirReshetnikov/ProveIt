#!/usr/bin/env python3
"""Seal the portable component; exclude only caches and the self/ephemeral receipts."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
files=[]
for p in sorted(ROOT.rglob('*')):
    rel=p.relative_to(ROOT)
    if not p.is_file() or '__pycache__' in rel.parts or rel.name.endswith('.pyc'):continue
    if str(rel) in ('MANIFEST_SHA256.json','REPLAY.json'):continue
    raw=p.read_bytes();files.append({'path':str(rel),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
(ROOT/'MANIFEST_SHA256.json').write_text(json.dumps({'schema':'sha256-manifest-v1','files':files,
  'excluded':['MANIFEST_SHA256.json (self)','REPLAY.json (fresh replay result)','__pycache__ and *.pyc']},indent=2)+'\n')
print(json.dumps({'status':'PASS','files':len(files)}))
