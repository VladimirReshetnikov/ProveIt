#!/usr/bin/env python3
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parent.parent
lines = (ROOT/'SHA256SUMS').read_text().splitlines()
for line in lines:
    digest, name = line.split('  ', 1)
    assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
print(f'All {len(lines)} frozen file hashes verified')
