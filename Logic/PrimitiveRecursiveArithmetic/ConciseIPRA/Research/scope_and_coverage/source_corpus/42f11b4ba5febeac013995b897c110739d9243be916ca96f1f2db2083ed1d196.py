"""Verify the delivered payload before rebuilding or experimenting."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
failures = []
for item in manifest['files']:
    path = ROOT / item['path']
    if not path.is_file():
        failures.append({'path': item['path'], 'error': 'missing'})
        continue
    data = path.read_bytes()
    if len(data) != item['bytes'] or hashlib.sha256(data).hexdigest() != item['sha256']:
        failures.append({'path': item['path'], 'error': 'content mismatch'})
print(json.dumps({'checked': len(manifest['files']), 'failures': failures}, indent=2))
if failures:
    raise SystemExit(1)
