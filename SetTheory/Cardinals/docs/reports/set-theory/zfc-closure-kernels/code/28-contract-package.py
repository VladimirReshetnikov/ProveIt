#!/usr/bin/env python3
"""Create a sorted ZIP and content manifest from the finished report directory.

The PDF must already exist. Zip metadata is fixed for reproducibility of the
same input bytes. Rebuilding the PDF can change its own producer metadata.
"""
from pathlib import Path
import argparse
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent
LATEX_TEMP = {'report.aux', 'report.fdb_latexmk', 'report.fls', 'report.log',
              'report.out', 'report.toc', 'report.synctex.gz'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT.parent/'zfc_contraction_research.zip')
    args = parser.parse_args()
    destination = args.output.resolve()
    if not (ROOT/'report.pdf').is_file():
        raise SystemExit('Build report.pdf before packaging.')
    if destination.is_relative_to(ROOT):
        raise SystemExit('Write the ZIP outside the report directory.')
    files = sorted(p for p in ROOT.rglob('*') if p.is_file()
                   and '__pycache__' not in p.parts and p.suffix != '.pyc'
                   and not (p.parent == ROOT and p.name in LATEX_TEMP)
                   and p != ROOT/'SHA256SUMS')
    (ROOT/'SHA256SUMS').write_text(''.join(
        f'{digest(p)}  {p.relative_to(ROOT).as_posix()}\n' for p in files))
    files = sorted(files + [ROOT/'SHA256SUMS'])
    destination.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(destination, 'w', compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for path in files:
            name = ROOT.name + '/' + path.relative_to(ROOT).as_posix()
            item = zipfile.ZipInfo(name, date_time=(2026, 10, 16, 0, 0, 0))
            item.create_system = 3
            item.external_attr = 0o100644 << 16
            item.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(item, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED,
                             compresslevel=9)
    with zipfile.ZipFile(destination) as archive:
        if archive.testzip() is not None:
            raise SystemExit('ZIP integrity test failed.')
    print(json.dumps({'archive': str(destination), 'files': len(files),
                      'bytes': destination.stat().st_size,
                      'sha256': digest(destination)}, indent=2))


if __name__ == '__main__':
    main()
