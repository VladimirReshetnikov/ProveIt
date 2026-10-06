#!/usr/bin/env python3
"""Create a deterministic Report219 archive from its explicit public file set."""
from pathlib import Path
import argparse
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent
TOP = ('Report219.tex', 'Report219.pdf', 'README.md', 'build_pdf.py',
       'build_archive.py', 'verify_package.py', 'toolchain.json')


def payload():
    paths = [ROOT/name for name in TOP]
    for dirname in ('code', 'reference_receipts'):
        directory = ROOT/dirname
        if not directory.is_dir():
            raise ValueError('Missing public directory '+dirname)
        paths += sorted(p for p in directory.rglob("*") if p.is_file() and p.suffix in ('.py', '.json', '.md', '.txt') and '__pycache__' not in p.parts)
    if not paths or any(not p.is_file() or p.is_symlink() for p in paths):
        raise ValueError('Every package input must be an ordinary non-symlink file')
    files = {str(p.relative_to(ROOT)): p.read_bytes() for p in paths}
    manifest = {'schema_version': 1, 'report': 'Report219',
                'files': {name: {'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
                          for name, data in sorted(files.items())}}
    files['MANIFEST.json'] = (json.dumps(manifest, indent=2, sort_keys=True)+'\n').encode()
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path, help='fresh ZIP path')
    args = parser.parse_args()
    if args.output.exists():
        parser.error('output must not exist')
    files = payload()
    with args.output.open('xb') as stream:
        with zipfile.ZipFile(stream, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
            for name, data in sorted(files.items()):
                info = zipfile.ZipInfo('Report219/'+name, date_time=(2026, 10, 4, 0, 0, 0))
                info.create_system = 3
                info.external_attr = 0o100644 << 16
                info.compress_type = zipfile.ZIP_DEFLATED
                archive.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    print('PASS: deterministic archive '+str(args.output))


if __name__ == '__main__':
    main()
