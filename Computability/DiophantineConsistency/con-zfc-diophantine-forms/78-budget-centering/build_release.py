#!/usr/bin/env python3
"""Write a SHA-256 content manifest and a clean ZIP of this package.

ZIP metadata is fixed, so identical input files give an identical archive.
The existing PDF is included. Run make first to rebuild it if necessary.
"""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent
BUILD_SUFFIXES = {'.aux', '.log', '.out', '.toc', '.fls', '.fdb_latexmk', '.pyc'}


def delivered(path):
    relative = path.relative_to(ROOT)
    return (path.is_file() and '__pycache__' not in relative.parts
            and path.suffix not in BUILD_SUFFIXES
            and path.name != 'MANIFEST.sha256')


def main():
    files = sorted(path for path in ROOT.rglob('*') if delivered(path))
    manifest = ROOT / 'MANIFEST.sha256'
    manifest.write_text(''.join(
        hashlib.sha256(path.read_bytes()).hexdigest() + '  '
        + path.relative_to(ROOT).as_posix() + '\n' for path in files))
    files.append(manifest)
    target = ROOT.parent / (ROOT.name + '.zip')
    with zipfile.ZipFile(target, 'w', compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for path in sorted(files):
            name = ROOT.name + '/' + path.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 23, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(target) as archive:
        bad = archive.testzip()
        if bad is not None:
            raise RuntimeError('ZIP CRC failure: ' + bad)
        for line in manifest.read_text().splitlines():
            digest, name = line.split('  ', 1)
            actual = hashlib.sha256(archive.read(ROOT.name + '/' + name)).hexdigest()
            if actual != digest:
                raise RuntimeError('Manifest mismatch: ' + name)
    print(json.dumps({'archive': str(target), 'files': len(files),
                      'bytes': target.stat().st_size,
                      'sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                      'zip_crc_and_all_manifest_hashes': 'PASS'}, indent=2))


if __name__ == '__main__':
    main()
