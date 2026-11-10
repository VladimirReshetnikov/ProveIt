"""Create a deterministic archive and verify its complete SHA-256 manifest.

This is an untrusted packaging utility, not part of the proof checker.
"""
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent


def selected_files():
    return sorted(
        path for path in ROOT.rglob('*')
        if path.is_file()
        and '__pycache__' not in path.parts
        and path.suffix not in {'.pyc', '.pyo', '.zip'}
        and path.name != 'MANIFEST.json'
    )


def main():
    files = selected_files()
    rows = []
    for path in files:
        raw = path.read_bytes()
        rows.append({'path': path.relative_to(ROOT).as_posix(),
                     'bytes': len(raw),
                     'sha256': hashlib.sha256(raw).hexdigest()})
    manifest = ROOT / 'MANIFEST.json'
    manifest.write_text(json.dumps({
        'format': 'sha256-file-manifest-v1',
        'scope': 'All archive files except this manifest itself.',
        'files': rows,
    }, indent=2) + '\n')
    files.append(manifest)
    destination = ROOT.parent / (ROOT.name + '.zip')
    with zipfile.ZipFile(destination, 'w', compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for path in sorted(files):
            name = ROOT.name + '/' + path.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(name, date_time=(2026, 11, 10, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(destination) as archive:
        bad = archive.testzip()
        if bad is not None:
            raise ValueError('CRC failure: ' + bad)
        for row in rows:
            raw = archive.read(ROOT.name + '/' + row['path'])
            if len(raw) != row['bytes'] or hashlib.sha256(raw).hexdigest() != row['sha256']:
                raise ValueError('Manifest failure: ' + row['path'])
    print(json.dumps({'archive': str(destination),
                      'bytes': destination.stat().st_size,
                      'files': len(files),
                      'sha256': hashlib.sha256(destination.read_bytes()).hexdigest(),
                      'crc_and_manifest_verified': True}, indent=2))


if __name__ == '__main__':
    main()
