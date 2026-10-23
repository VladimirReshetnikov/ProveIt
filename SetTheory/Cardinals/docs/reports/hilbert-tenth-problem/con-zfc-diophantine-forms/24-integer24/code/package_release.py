#!/usr/bin/env python3
"""Write a checksum ledger and a deterministic ZIP of the complete deliverable.

Run after verification and PDF compilation. Build intermediates and Python
bytecode are excluded. File data are never modified to improve compression.
The ledger excludes itself; the archive is written next to the package root.
"""
from hashlib import sha256
from pathlib import Path
import json
import zipfile

ROOT = Path(__file__).resolve().parent.parent
ARCHIVE = ROOT.parent / 'con_zfc_synthesis_2026-10-22.zip'
EXCLUDED_SUFFIXES = {'.aux', '.log', '.out', '.toc', '.pyc', '.synctex', '.fls', '.fdb_latexmk'}


def included(path):
    rel = path.relative_to(ROOT)
    return (path.is_file() and '__pycache__' not in rel.parts
            and path.suffix not in EXCLUDED_SUFFIXES
            and not path.name.endswith('.synctex.gz')
            and not any(part.startswith('.') for part in rel.parts))


def main():
    files = sorted(p for p in ROOT.rglob('*') if included(p) and p.name != 'SHA256SUMS')
    lines = [sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(ROOT).as_posix() for p in files]
    (ROOT / 'SHA256SUMS').write_text('\n'.join(lines) + '\n', encoding='utf-8')
    files = sorted(files + [ROOT / 'SHA256SUMS'])
    with zipfile.ZipFile(ARCHIVE, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as out:
        for path in files:
            name = ROOT.name + '/' + path.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 22, 12, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            out.writestr(info, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    with zipfile.ZipFile(ARCHIVE) as check:
        bad = check.testzip()
        if bad is not None:
            raise RuntimeError('ZIP CRC failure: ' + bad)
    print(json.dumps({'archive': str(ARCHIVE), 'files': len(files),
                      'bytes': ARCHIVE.stat().st_size,
                      'sha256': sha256(ARCHIVE.read_bytes()).hexdigest()}, indent=2))


if __name__ == '__main__':
    main()
