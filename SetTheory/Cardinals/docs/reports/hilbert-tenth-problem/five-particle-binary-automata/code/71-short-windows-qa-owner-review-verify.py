"""Owned read-only review-dossier authentication; no scientific code is loaded."""
import hashlib
import json
from pathlib import Path
import stat
import sys

if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):
    raise ValueError("Use python3 -I -S -B")
root = Path('/workspace/shared/report71-independent-release-tools-review-20261004/sealed-review')
seal = root / 'REVIEW_SEAL.json'
raw = seal.read_bytes()
pin = '3a295cac3b514579cf8d9f8e094b5d5ca2ec41057e3c2efc41744dc70a81b28d'
if hashlib.sha256(raw).hexdigest() != pin:
    raise ValueError('Review seal pin mismatch')
rows = json.loads(raw)['files']
actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
if actual != set(rows) | {'REVIEW_SEAL.json', 'REVIEW_SEAL.json.sha256'}:
    raise ValueError('Review inventory mismatch')
for name, row in rows.items():
    if Path(name).is_absolute() or any(part in ('', '.', '..') for part in name.split('/')):
        raise ValueError('Unsafe review path')
    path = root / name
    if not stat.S_ISREG(path.lstat().st_mode) or path.lstat().st_nlink != 1:
        raise ValueError('Unsafe review object')
    data = path.read_bytes()
    if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
        raise ValueError('Review payload mismatch: ' + name)
copy = Path('/workspace/shared/report71-short-exactness-release-20261004/qa/release-tools-review')
for source in [root, *sorted(root.rglob('*'))]:
    target = copy / source.relative_to(root)
    a, b = source.lstat(), target.lstat()
    if (a.st_mode, a.st_mtime_ns) != (b.st_mode, b.st_mtime_ns):
        raise ValueError('Copied review metadata mismatch')
    if stat.S_ISREG(a.st_mode) and source.read_bytes() != target.read_bytes():
        raise ValueError('Copied review bytes mismatch')
print(json.dumps({'status': 'PASS', 'review_seal_sha256': pin, 'files': len(rows), 'copy_bytes_modes_mtimes_equal': True}, sort_keys=True))
