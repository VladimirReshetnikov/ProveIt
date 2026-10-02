"""Verify the SHA-256 manifest shipped with the report (Python standard library)."""
import hashlib
from pathlib import Path

root = Path(__file__).resolve().parents[1]
manifest = root / 'SHA256SUMS'
seen = set()
for line in manifest.read_text().splitlines():
    expected, name = line.split('  ', 1)
    relative = Path(name)
    if relative.is_absolute() or '..' in relative.parts or name in seen:
        raise ValueError('Unsafe or duplicate manifest entry: '+name)
    seen.add(name)
    path = root / relative
    assert path.is_file() and not path.is_symlink(), name
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    assert actual == expected, f'{name}: {actual} != {expected}'
print(f'PASS: {len(seen)} shipped SHA-256 hashes')
