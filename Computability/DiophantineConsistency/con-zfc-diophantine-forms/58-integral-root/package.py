#!/usr/bin/env python3
"""Create the deterministic delivery ZIP and its internal SHA-256 manifest."""
import hashlib
import json
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EXCLUDED_SUFFIXES = {'.aux', '.log', '.out', '.toc', '.fls', '.fdb_latexmk', '.pyc'}


def include(path):
    rel = path.relative_to(ROOT)
    return (path.is_file() and '__pycache__' not in rel.parts
            and not any(part.startswith('.') for part in rel.parts)
            and path.suffix not in EXCLUDED_SUFFIXES
            and not path.name.endswith('.synctex.gz')
            and rel.as_posix() != 'MANIFEST.sha256')


def main():
    files = sorted(p for p in ROOT.rglob('*') if include(p))
    manifest = ROOT/'MANIFEST.sha256'
    lines = [hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(ROOT).as_posix()
             for p in files]
    manifest.write_text('\n'.join(lines)+'\n')
    files = sorted(files+[manifest])
    archive = ROOT.with_suffix('.zip')
    with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
        for path in files:
            name = ROOT.name+'/'+path.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 23, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            zf.writestr(info, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    with zipfile.ZipFile(archive) as zf:
        if zf.testzip() is not None:
            raise ValueError('ZIP CRC verification failed')
        for path in files:
            name = ROOT.name+'/'+path.relative_to(ROOT).as_posix()
            if zf.read(name) != path.read_bytes():
                raise ValueError('ZIP byte mismatch: '+name)
    print(json.dumps({'archive': str(archive), 'files': len(files),
                      'bytes': archive.stat().st_size,
                      'sha256': hashlib.sha256(archive.read_bytes()).hexdigest(),
                      'member_byte_checks': 'PASS'}, indent=2))


if __name__ == '__main__':
    main()
