"""Write checksums for distributable package files."""
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OMIT = {'.aux', '.log', '.out', '.toc', '.pyc'}
lines = []
for path in sorted(ROOT.rglob('*')):
    if (not path.is_file() or '__pycache__' in path.parts or path.suffix in OMIT
            or path.name == 'SHA256SUMS'):
        continue
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    lines.append(digest + '  ' + path.relative_to(ROOT).as_posix())
(ROOT / 'SHA256SUMS').write_text('\n'.join(lines) + '\n')
print('Checksummed', len(lines), 'files.')
