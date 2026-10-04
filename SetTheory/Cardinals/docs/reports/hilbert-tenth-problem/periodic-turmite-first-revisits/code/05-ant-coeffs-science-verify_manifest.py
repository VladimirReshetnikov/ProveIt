#!/usr/bin/env python3
"""Check package byte identities only; never import any scientific source."""
import hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parent
manifest=json.loads((ROOT/'MANIFEST.json').read_text())
for rel,expected in manifest['files'].items():
    path=ROOT/rel
    if not path.is_file() or path.is_symlink() or ROOT not in path.resolve().parents:
        raise ValueError(('invalid package file',rel))
    data=path.read_bytes()
    if len(data)!=expected['bytes'] or hashlib.sha256(data).hexdigest()!=expected['sha256']:
        raise ValueError(('package identity mismatch',rel))
print(json.dumps({'status':'PASS_PACKAGE_IDENTITIES','files':len(manifest['files'])}))
