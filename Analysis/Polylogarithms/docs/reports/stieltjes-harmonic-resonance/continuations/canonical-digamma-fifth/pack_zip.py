#!/usr/bin/env python3
"""Package the reviewed deliverables, excluding caches and TeX build products."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent
STEM = 'Canonical_Digamma_and_Fifth_Moment'
TOP = ['README.md', 'requirements.txt', 'article.tex', 'references.tex',
       'build.py', 'verify_all.py', 'pack_zip.py', 'claims.json',
       STEM + '.tex', STEM + '.pdf']


def selected_files():
    files = [ROOT / name for name in TOP]
    for dirname in ['sections', 'code', 'results', 'provenance', 'integration']:
        for path in (ROOT / dirname).rglob('*'):
            if not path.is_file() or '__pycache__' in path.parts:
                continue
            if dirname == 'results' and path.suffix != '.json':
                continue
            if path.suffix in {'.tex', '.py', '.json', '.md', '.txt'}:
                files.append(path)
    for path in files:
        if not path.is_file():
            raise FileNotFoundError(path)
    return sorted(set(files), key=lambda p: p.relative_to(ROOT).as_posix())


def main():
    files = selected_files()
    records = [{'path': p.relative_to(ROOT).as_posix(), 'size_bytes': p.stat().st_size,
                'sha256': hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]
    manifest = ROOT / 'package_manifest.json'
    manifest.write_text(json.dumps({'title': 'Canonical Digamma Polynomials and the Fifth Harmonic Bridge',
                                   'date': '2026-10-11', 'files': records}, indent=2) + '\n')
    files.append(manifest)
    hashes = ROOT / 'SHA256SUMS'
    hashes.write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  '
                             + p.relative_to(ROOT).as_posix() + '\n'
                             for p in sorted(files)))
    files.append(hashes)
    target = ROOT.parent / (ROOT.name + '.zip')
    with zipfile.ZipFile(target, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in sorted(files):
            name = ROOT.name + '/' + path.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 11, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(target) as archive:
        if archive.testzip() is not None:
            raise RuntimeError('ZIP CRC verification failed.')
        for line in hashes.read_text().splitlines():
            digest, name = line.split('  ', 1)
            actual = hashlib.sha256(archive.read(ROOT.name + '/' + name)).hexdigest()
            if actual != digest:
                raise RuntimeError('ZIP member hash mismatch: ' + name)
    print(json.dumps({'zip': target.name, 'members': len(files),
                      'size_bytes': target.stat().st_size,
                      'sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                      'crc_and_member_hashes_verified': True}, indent=2))


if __name__ == '__main__':
    main()
