"""Verify SHA-256 content manifests with strict in-tree regular-file checks."""
from pathlib import Path, PurePosixPath
import hashlib, sys
base=Path(__file__).resolve().parents[1]
manifest=base/(sys.argv[1] if len(sys.argv)>1 else 'MANIFEST.sha256')
seen=set()
for line in manifest.read_text().splitlines():
    if not line: continue
    digest,name=line.split('  ',1)
    path=PurePosixPath(name)
    assert not path.is_absolute() and '..' not in path.parts and name not in seen,name
    seen.add(name); actual=base.joinpath(*path.parts)
    assert actual.is_file() and not actual.is_symlink(),name
    assert actual.resolve().is_relative_to(base.resolve()),name
    assert hashlib.sha256(actual.read_bytes()).hexdigest()==digest,name
print(f'PASS: {len(seen)} pinned files in {manifest.name}')
