"""Verify the original delivered payload against its SHA-256 manifest."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
records = json.loads((root / 'MANIFEST.json').read_text())['files']
failures = []
for record in records:
    path = root / record['path']
    if not path.is_file():
        failures.append(record['path'] + ': missing')
        continue
    content = path.read_bytes()
    if len(content) != record['bytes'] or hashlib.sha256(content).hexdigest() != record['sha256']:
        failures.append(record['path'] + ': changed')
if failures:
    raise SystemExit('\n'.join(failures))
print('PASS: all {} original payload files match.'.format(len(records)))
