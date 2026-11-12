"""Verify the delivered manifest; generated evidence may change after reproduction."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    raw = path.read_bytes()
    if len(raw) != item['bytes'] or hashlib.sha256(raw).hexdigest() != item['sha256']:
        raise SystemExit('Manifest mismatch: ' + item['path'])
print('VERIFIED', len(manifest['files']), 'files')
