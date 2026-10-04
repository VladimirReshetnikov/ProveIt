"""Verify frozen local research packet bytes; no source execution or networking."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
manifest=json.loads((root/'MANIFEST.json').read_text())
for entry in manifest['files']:
    p=root/entry['path']
    if not p.is_file():raise RuntimeError('Missing file: '+entry['path'])
    b=p.read_bytes()
    if len(b)!=entry['bytes'] or hashlib.sha256(b).hexdigest()!=entry['sha256']:
        raise RuntimeError('Manifest mismatch: '+entry['path'])
print(json.dumps({'status':'PASS','files':len(manifest['files']),'scope':manifest['scope']},indent=2))
