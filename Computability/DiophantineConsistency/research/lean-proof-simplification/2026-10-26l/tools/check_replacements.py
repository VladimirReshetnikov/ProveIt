#!/usr/bin/env python3
"""Check that a checkout contains the exact replacement sources in this packet."""
import hashlib
import json
from pathlib import Path
import sys

bundle = Path(__file__).resolve().parents[1]
repository = Path(sys.argv[1] if len(sys.argv) > 1 else '.').resolve()
manifest = json.loads((bundle / 'validation/manifest.json').read_text())
failures = []
for item in manifest['files']:
    path = repository / item['path']
    if not path.is_file():
        failures.append(f"Missing: {item['path']}")
    elif hashlib.sha256(path.read_bytes()).hexdigest() != item['after_sha256']:
        failures.append(f"Content differs from checked replacement: {item['path']}")
if failures:
    print('\n'.join(failures), file=sys.stderr)
    raise SystemExit(1)
print('All six replacement source hashes match the verified packet.')
