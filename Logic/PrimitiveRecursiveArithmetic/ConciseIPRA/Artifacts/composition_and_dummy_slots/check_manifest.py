"""Verify the distributed archive before regenerating any outputs."""
from pathlib import Path
import hashlib
import sys

root = Path(__file__).resolve().parent
failures = []
count = 0
for line in (root / 'MANIFEST.sha256').read_text().splitlines():
    expected, name = line.split('  ', 1)
    path = root / name
    count += 1
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        failures.append(name)
if failures:
    print('FAILED:', *failures, sep='\n')
    sys.exit(1)
print(f'OK: {count} files match the SHA-256 manifest')
