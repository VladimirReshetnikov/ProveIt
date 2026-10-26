#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
rows=[]
for p in sorted(ROOT.rglob('*')):
 if not p.is_file() or '__pycache__' in p.parts or p.suffix=='.pyc' or p==ROOT/'MANIFEST_SHA256.json' or p==ROOT/'REPLAY.json':continue
 rows.append({'path':str(p.relative_to(ROOT)),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(ROOT/'MANIFEST_SHA256.json').write_text(json.dumps({'files':rows},indent=2)+'\n')
print(len(rows))
