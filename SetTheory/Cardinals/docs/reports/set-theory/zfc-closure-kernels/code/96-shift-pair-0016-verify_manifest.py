"""Verify all sealed distributed files; generated and recovered data are separate."""
from pathlib import Path, PurePosixPath
import hashlib, sys
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions must be enabled; do not use -O or PYTHONOPTIMIZE.')
ROOT=Path(__file__).resolve().parents[1]
def main():
    count=0
    for line in (ROOT/'MANIFEST.sha256').read_text().splitlines():
        expected,rel=line.split('  ',1)
        path=PurePosixPath(rel)
        if path.is_absolute() or '..' in path.parts:
            raise ValueError('Unsafe manifest path')
        target=(ROOT/rel).resolve()
        if not target.is_relative_to(ROOT):
            raise ValueError('Manifest path escapes package')
        actual=hashlib.sha256(target.read_bytes()).hexdigest()
        if actual!=expected:
            raise ValueError('Distributed file differs: '+rel)
        count+=1
    print(f'PASS: {count} distributed files match MANIFEST.sha256')
if __name__=='__main__':
    main()
