"""Rebuild the manifest and ZIP, excluding temporary and Python cache files."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent
excluded = {'tmp', '__pycache__', '.git'}
payload = sorted(path for path in ROOT.rglob('*')
                 if path.is_file()
                 and not (set(path.relative_to(ROOT).parts) & excluded)
                 and path.name != 'MANIFEST.json'
                 and path.suffix not in {'.pyc', '.pyo', '.zip'})
rows = []
for path in payload:
    data = path.read_bytes()
    rows.append({'path': path.relative_to(ROOT).as_posix(),
                 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()})
manifest = ROOT / 'MANIFEST.json'
manifest.write_text(json.dumps({'format': 1, 'hash': 'SHA-256',
                               'exclusions': ['MANIFEST.json itself', 'tmp/',
                                              '__pycache__/', '*.pyc', '*.pyo', '*.zip'],
                               'files': rows}, indent=2) + '\n')
archive = ROOT.parent / (ROOT.name + '.zip')
with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED,
                     compresslevel=9) as output:
    for path in sorted(payload + [manifest]):
        name = ROOT.name + '/' + path.relative_to(ROOT).as_posix()
        entry = zipfile.ZipInfo(name, date_time=(2026, 11, 10, 0, 0, 0))
        entry.compress_type = zipfile.ZIP_DEFLATED
        entry.external_attr = 0o100644 << 16
        output.writestr(entry, path.read_bytes(), compresslevel=9)
data = archive.read_bytes()
print(json.dumps({'archive': str(archive), 'payload_files': len(rows),
                  'zip_entries': len(rows) + 1, 'bytes': len(data),
                  'sha256': hashlib.sha256(data).hexdigest()}, indent=2))
