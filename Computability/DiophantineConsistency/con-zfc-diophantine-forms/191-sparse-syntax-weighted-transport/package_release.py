#!/usr/bin/env python3
"""Rebuild the release manifest and a deterministic ZIP of the package."""
from pathlib import Path
import argparse
import hashlib
import zipfile

ROOT = Path(__file__).resolve().parent
EXCLUDED_SUFFIXES = {'.aux', '.log', '.toc', '.out', '.fls', '.fdb_latexmk', '.pyc'}


def release_files():
    return sorted(path for path in ROOT.rglob('*') if path.is_file()
                  and path.name != 'MANIFEST.sha256'
                  and path.suffix not in EXCLUDED_SUFFIXES
                  and '__pycache__' not in path.parts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-only', action='store_true')
    parser.add_argument('--output', type=Path, default=None)
    args = parser.parse_args()
    files = release_files()
    manifest = ROOT/'MANIFEST.sha256'
    manifest.write_text(''.join(hashlib.sha256(path.read_bytes()).hexdigest()+'  '+
                                path.relative_to(ROOT).as_posix()+'\n' for path in files))
    if args.manifest_only:
        print(f'Bound {len(files)} release files.')
        return
    destination = args.output or ROOT.with_suffix('.zip')
    if destination.resolve().is_relative_to(ROOT):
        raise ValueError('The release ZIP must be outside the package directory')
    with zipfile.ZipFile(destination, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in sorted(files+[manifest]):
            item = zipfile.ZipInfo(ROOT.name+'/'+path.relative_to(ROOT).as_posix(),
                                   date_time=(2026, 10, 26, 0, 0, 0))
            item.compress_type = zipfile.ZIP_DEFLATED
            item.external_attr = 0o100644 << 16
            archive.writestr(item, path.read_bytes())
    print(f'{destination.name}: {destination.stat().st_size} bytes; {len(files)+1} members.')


if __name__ == '__main__':
    main()
