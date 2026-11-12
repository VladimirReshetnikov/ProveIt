"""Check the delivered payload before running rebuilding commands."""
from pathlib import Path
import hashlib

ROOT = Path(__file__).resolve().parent
count = 0
for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
    expected, name = line.split('  ', 1)
    path = ROOT / name
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise SystemExit('Checksum mismatch: ' + name)
    count += 1
print('Verified', count, 'files')
