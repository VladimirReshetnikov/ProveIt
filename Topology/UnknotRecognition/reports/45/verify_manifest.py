"""Verify shipped artifact hashes; generated build files are ignored."""
from pathlib import Path
import hashlib
import sys
root = Path(__file__).resolve().parent
bad = []
lines = (root/'MANIFEST.sha256').read_text().splitlines()
for line in lines:
    expected, name = line.split('  ', 1)
    path = root/name
    actual = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else 'MISSING'
    if actual != expected:
        bad.append(name)
print(f'Checked {len(lines)} artifacts; mismatches: {len(bad)}')
for name in bad: print(name)
sys.exit(bool(bad))
