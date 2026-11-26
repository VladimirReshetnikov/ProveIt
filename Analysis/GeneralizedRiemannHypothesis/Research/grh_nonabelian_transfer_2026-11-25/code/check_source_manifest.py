#!/usr/bin/env python3
"""Verify the included unmodified upstream source files against their manifest."""
from pathlib import Path
import hashlib,json
base=Path(__file__).resolve().parents[1]
manifest=json.loads((base/'evidence/source_manifest.json').read_text())
for item in manifest['files']:
    data=(base/'evidence/upstream'/item['path']).read_bytes()
    assert len(data)==item['bytes'],item['path']
    assert hashlib.sha256(data).hexdigest()==item['sha256'],item['path']
    blob=b'blob '+str(len(data)).encode()+b'\0'+data
    assert hashlib.sha1(blob).hexdigest()==item['git_blob_sha1'],item['path']
print(json.dumps({'status':'passed','commit':manifest['commit'],
                  'verified_files':len(manifest['files'])},indent=2))
