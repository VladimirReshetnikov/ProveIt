"""Check every packaged file against SHA256SUMS; ignore local build caches."""
from pathlib import Path
import hashlib
root = Path(__file__).resolve().parent
records = {}
for line in (root / 'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ', 1)
    if name in records:
        raise SystemExit(f'Duplicate manifest entry: {name}')
    records[name] = digest

def packaged(p):
    rel = p.relative_to(root)
    return p.is_file() and rel.as_posix() != 'SHA256SUMS' and not any(
        part.startswith('.') or part == '__pycache__' for part in rel.parts
    ) and p.suffix != '.pyc'
actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if packaged(p)}
if actual != set(records):
    raise SystemExit(f'Manifest set mismatch: missing={set(records)-actual}, extra={actual-set(records)}')
for name, digest in records.items():
    observed = hashlib.sha256((root/name).read_bytes()).hexdigest()
    if observed != digest:
        raise SystemExit(f'Hash mismatch: {name}')
print(f'PASS: exact manifest file set and all {len(records)} SHA-256 hashes')
