"""Check the pinned package payload without shell filename assumptions."""
from pathlib import Path, PurePosixPath
import hashlib
root=Path(__file__).resolve().parent.parent
seen=set()
for line in (root/'SHA256SUMS').read_text().splitlines():
 digest,name=line.split('  ',1)
 p=PurePosixPath(name)
 assert len(digest)==64 and not p.is_absolute() and '..' not in p.parts
 assert name not in seen;seen.add(name)
 f=root.joinpath(*p.parts)
 assert f.is_file() and not f.is_symlink(),name
 assert hashlib.sha256(f.read_bytes()).hexdigest()==digest, 'Hash mismatch: '+name
print(f'PASS: {len(seen)} SHA-256-pinned payload files')
