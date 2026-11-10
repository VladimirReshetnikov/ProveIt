"""Package the sources, report, evidence and fixtures; exclude build caches."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT.with_suffix('.zip')


def deliverable(path):
    relative = path.relative_to(ROOT)
    return (path.is_file()
            and not any(part in ('build', '__pycache__') for part in relative.parts)
            and path.suffix not in ('.pyc', '.pyo')
            and path.name != 'MANIFEST.sha256.json')


files = sorted(path for path in ROOT.rglob('*') if deliverable(path))
manifest = {'algorithm': 'SHA-256', 'files': [
    {'path': path.relative_to(ROOT).as_posix(), 'bytes': path.stat().st_size,
     'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
    for path in files]}
manifest_path = ROOT / 'MANIFEST.sha256.json'
manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
with zipfile.ZipFile(ARCHIVE, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as out:
    for path in files + [manifest_path]:
        out.write(path, ROOT.name + '/' + path.relative_to(ROOT).as_posix())
with zipfile.ZipFile(ARCHIVE) as archive:
    if archive.testzip() is not None:
        raise SystemExit('Archive CRC verification failed')
    for row in manifest['files']:
        data = archive.read(ROOT.name + '/' + row['path'])
        if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
            raise SystemExit('Archive manifest verification failed: ' + row['path'])
print(json.dumps({'status': 'PASS', 'archive': str(ARCHIVE),
                  'members': len(files) + 1, 'bytes': ARCHIVE.stat().st_size,
                  'sha256': hashlib.sha256(ARCHIVE.read_bytes()).hexdigest()}, indent=2))
