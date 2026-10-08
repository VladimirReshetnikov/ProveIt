"""Verify every archived file against MANIFEST.sha256."""
from hashlib import sha256
from pathlib import Path
import sys

root = Path(__file__).resolve().parent
failures, checked = [], 0
for line in (root / 'MANIFEST.sha256').read_text().splitlines():
    expected, name = line.split('  ', 1)
    relative = Path(name)
    if relative.is_absolute() or '..' in relative.parts:
        raise SystemExit('Unsafe manifest path: ' + name)
    path = root / relative
    actual = sha256(path.read_bytes()).hexdigest() if path.is_file() else None
    if actual != expected:
        failures.append(name)
    checked += 1
if failures:
    print('Checksum failures:', *failures, sep='\n')
    sys.exit(1)
print('Verified', checked, 'files; all SHA-256 checksums match.')
