"""Verify SHA-256 hashes in the delivered manifest; no external dependencies."""
import hashlib
import json
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
manifest_path = ROOT/'MANIFEST.json'
try:
    manifest = json.loads(manifest_path.read_text())
except (OSError, ValueError) as error:
    raise SystemExit(f'Cannot read manifest: {error}')
errors = []
for item in manifest['files']:
    relative = Path(item['path'])
    if relative.is_absolute() or '..' in relative.parts:
        errors.append(f'unsafe path: {relative}')
        continue
    path = ROOT/relative
    try:
        data = path.read_bytes()
    except OSError as error:
        errors.append(f'{relative}: {error}')
        continue
    if len(data) != item['bytes'] or hashlib.sha256(data).hexdigest() != item['sha256']:
        errors.append(f'{relative}: hash/length mismatch')
if errors:
    print('\n'.join(errors), file=sys.stderr)
    raise SystemExit(1)
print(f"Verified {len(manifest['files'])} files.")
