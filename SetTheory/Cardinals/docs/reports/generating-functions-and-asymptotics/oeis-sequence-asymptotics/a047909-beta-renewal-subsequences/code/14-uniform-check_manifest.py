"""Verify safe relative paths and SHA-256 for every listed deliverable."""
from pathlib import Path, PurePosixPath
import hashlib, re, sys
root=Path(__file__).resolve().parents[1]
manifest=root/'SHA256SUMS'
seen=set()
for line in manifest.read_text().splitlines():
    match=re.fullmatch(r'([0-9a-f]{64})  (.+)',line)
    if not match:raise SystemExit('Invalid manifest line')
    digest,name=match.groups(); p=PurePosixPath(name)
    if p.is_absolute() or '..' in p.parts or '.' in p.parts or '\\' in name or name in seen:
        raise SystemExit('Unsafe or duplicate manifest path: '+name)
    seen.add(name); target=root.joinpath(*p.parts)
    if not target.is_file() or target.is_symlink():raise SystemExit('Missing or unsafe file: '+name)
    if root not in target.resolve().parents:raise SystemExit('Escaping path: '+name)
    actual=hashlib.sha256(target.read_bytes()).hexdigest()
    if actual!=digest:raise SystemExit('SHA-256 mismatch: '+name)
print(f'PASS: {len(seen)} manifest-pinned files')
