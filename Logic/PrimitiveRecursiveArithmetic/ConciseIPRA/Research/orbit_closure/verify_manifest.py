"""Verify the delivered bytes before running scripts that regenerate evidence."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
record = json.loads((ROOT / 'MANIFEST.json').read_text())
for name, expected in record['sha256'].items():
    actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    if actual != expected:
        raise ValueError(('Changed file', name, expected, actual))
print('Verified', len(record['sha256']), 'files')
