"""Verify the original delivered payload before rebuilding or editing it."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
failures = []
for row in manifest['files']:
    path = ROOT / row['path']
    if not path.is_file():
        failures.append({'path': row['path'], 'error': 'missing'})
        continue
    data = path.read_bytes()
    if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
        failures.append({'path': row['path'], 'error': 'bytes differ'})
print(json.dumps({'verified_files': len(manifest['files']), 'failures': failures}, indent=2))
if failures:
    raise SystemExit(1)
