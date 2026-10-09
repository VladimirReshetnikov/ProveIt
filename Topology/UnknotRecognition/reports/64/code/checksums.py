"""Create or verify a stable source/artifact manifest; excludes TeX sidecars."""
from pathlib import Path
from hashlib import sha256
import argparse

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--verify', action='store_true')
args = parser.parse_args()


def files():
    excluded = {'.aux', '.log', '.out', '.toc', '.pyc'}
    for p in sorted(root.rglob('*')):
        if p.is_file() and p.name != 'SHA256SUMS' and p.suffix not in excluded and '__pycache__' not in p.parts:
            yield p


lines = [sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(root).as_posix() for p in files()]
manifest = '\n'.join(lines)+'\n'
if args.verify:
    good = (root/'SHA256SUMS').read_text() == manifest
    print('Manifest matches all packaged files.' if good else 'MANIFEST MISMATCH')
    raise SystemExit(0 if good else 1)
(root/'SHA256SUMS').write_text(manifest)
print(f'Hashed {len(lines)} files.')
