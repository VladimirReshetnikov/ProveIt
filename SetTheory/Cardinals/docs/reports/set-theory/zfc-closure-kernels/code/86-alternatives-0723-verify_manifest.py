#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parent
manifest=json.loads((root/'MANIFEST.sha256.json').read_text());bad=[]
for item in manifest['files']:
 p=root/item['path']
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=item['sha256']:bad.append(item['path'])
print('Verified',len(manifest['files']),'files;' if not bad else 'files with failures:',bad)
sys.exit(bool(bad))
