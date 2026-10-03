"""Verify all distributed file hashes; reject unsafe paths and symlinks."""
from pathlib import Path, PurePosixPath
import hashlib
import re

ROOT = Path(__file__).resolve().parent

def verify():
    manifest = ROOT/'MANIFEST.sha256'
    entries = []
    seen = set()
    for line in manifest.read_text().splitlines():
        digest, name = line.split('  ',1)
        p = PurePosixPath(name)
        assert re.fullmatch(r'[0-9a-f]{64}',digest), 'Invalid checksum'
        assert not p.is_absolute() and '..' not in p.parts and '.' not in p.parts
        assert '\\' not in name and name not in seen and name != 'MANIFEST.sha256'
        seen.add(name)
        target = ROOT.joinpath(*p.parts)
        assert target.is_file() and not target.is_symlink(), f'Invalid file: {name}'
        for ancestor in target.parents:
            if ancestor == ROOT:
                break
            assert not ancestor.is_symlink(), f'Linked directory: {name}'
        assert target.resolve().is_relative_to(ROOT), f'Escaping path: {name}'
        assert hashlib.sha256(target.read_bytes()).hexdigest() == digest, f'Hash mismatch: {name}'
        entries.append(name)
    return entries

if __name__ == '__main__':
    print(f'Verified {len(verify())} files in MANIFEST.sha256.')
