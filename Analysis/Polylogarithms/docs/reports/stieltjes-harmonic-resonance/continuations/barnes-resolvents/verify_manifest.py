"""Verify hashes of delivered files. Run before scripts overwrite result JSON."""
from pathlib import Path
import hashlib
import json

root=Path(__file__).resolve().parent
manifest=json.loads((root/'package_manifest.json').read_text())
bad=[]
for row in manifest['files']:
    path=root/row['path']
    if not path.is_file():
        bad.append((row['path'],'missing'))
        continue
    raw=path.read_bytes()
    if len(raw)!=row['bytes'] or hashlib.sha256(raw).hexdigest()!=row['sha256']:
        bad.append((row['path'],'hash or size mismatch'))
if bad:
    print(json.dumps({'ok':False,'differences':bad},indent=2))
    raise SystemExit(1)
print(json.dumps({'ok':True,'files_checked':len(manifest['files'])},indent=2))
