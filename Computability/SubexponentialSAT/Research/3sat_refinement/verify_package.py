#!/usr/bin/env python3
"""Rerun finite algebraic checks and verify packaged SHA-256 digests."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

root = Path(__file__).resolve().parent
for filename in ['parity_lift.py', 'weighted_partitions.py']:
    run = subprocess.run([sys.executable, str(root / 'code' / filename)],
                         check=True, capture_output=True, text=True)
    result = json.loads(run.stdout)
    if result.get('status') != 'all checks passed':
        raise RuntimeError(result)
    print(filename + ': all checks passed')
checked = 0
for line in (root / 'SHA256SUMS').read_text().splitlines():
    digest, relative = line.split('  ', 1)
    path = root / relative
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != actual:
        raise RuntimeError('Digest mismatch: ' + relative)
    checked += 1
print(str(checked) + ' file hashes verified')
