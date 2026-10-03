"""Verify all manifest-pinned payload files without traversing unsafe paths."""
import hashlib, json, sys
from pathlib import Path, PurePosixPath
root = Path(sys.argv[1] if len(sys.argv)>1 else Path(__file__).resolve().parents[1]).resolve()
manifest = json.loads((root/'MANIFEST.json').read_text())
for name, info in manifest['files'].items():
    p=PurePosixPath(name)
    assert not p.is_absolute() and '..' not in p.parts and '\\' not in name, name
    path=root.joinpath(*p.parts)
    assert not path.is_symlink() and path.is_file(), name
    assert root in path.resolve().parents, name
    data=path.read_bytes()
    assert len(data)==info['size'], name
    assert hashlib.sha256(data).hexdigest()==info['sha256'], name
print(f"PASS: {len(manifest['files'])} manifest-pinned files")
