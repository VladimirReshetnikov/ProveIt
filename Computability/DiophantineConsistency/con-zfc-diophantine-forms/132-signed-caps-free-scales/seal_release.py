#!/usr/bin/env python3
"""Maintainer action: inventory the finished tree; never a mathematical proof."""
import json,hashlib
from pathlib import Path
import reproduce as R
ROOT=Path(__file__).resolve().parent
files=[]
for rel,p in sorted(R.inventory(ROOT).items()):
    raw=p.read_bytes();files.append({'path':rel,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
(ROOT/'MANIFEST.json').write_text(json.dumps({'schema':'research_release_manifest_v1','exclusions':['MANIFEST.json (self)','__pycache__ and *.pyc (not distributed)'],'files':files},indent=2)+'\n')
print(json.dumps({'files':len(files),'bytes':sum(r['bytes'] for r in files)}))
