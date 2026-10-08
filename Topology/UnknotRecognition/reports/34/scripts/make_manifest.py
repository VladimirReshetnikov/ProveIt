"""Generate the release manifest after rebuilding and checking all artifacts."""
import hashlib
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
ignored_suffixes = {'.pyc', '.pyo', '.aux', '.log', '.out', '.toc', '.fls', '.fdb_latexmk'}
files = []
for path in sorted(ROOT.rglob('*')):
    if not path.is_file() or '__pycache__' in path.parts:
        continue
    if path.name == 'MANIFEST.json' or path.suffix in ignored_suffixes:
        continue
    data = path.read_bytes()
    files.append({'path': path.relative_to(ROOT).as_posix(), 'bytes': len(data),
                  'sha256': hashlib.sha256(data).hexdigest()})
(ROOT/'MANIFEST.json').write_text(json.dumps({'algorithm': 'SHA-256', 'files': files}, indent=2)+'\n')
print(f'Manifest contains {len(files)} files.')
