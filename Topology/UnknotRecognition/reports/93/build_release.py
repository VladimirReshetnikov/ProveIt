#!/usr/bin/env python3
"""Build the additive research archive and its content manifest.

Run after compiling the article and copying the final PDF to the package root.
This does not rerun mathematical experiments or modify upstream source.
"""

import hashlib
import json
from pathlib import Path
import zipfile


ROOT = Path(__file__).resolve().parent
ARCHIVE_NAME = 'ProveIt_Genus_Budgets_Native_Interfaces_2026-10-12.zip'
PREFIX = 'unknot_hierarchy_primitives'
EXCLUDED_PARTS = {'build', '__pycache__', '.pytest_cache'}
EXCLUDED_NAMES = {'results/focused_validation_summary.json'}


def release_files():
    return [p for p in sorted(ROOT.rglob('*'))
            if p.is_file()
            and not (set(p.relative_to(ROOT).parts) & EXCLUDED_PARTS)
            and not any(part.startswith('.') for part in p.relative_to(ROOT).parts)
            and p.relative_to(ROOT).as_posix() not in EXCLUDED_NAMES
            and p.suffix not in {'.pyc', '.zip'}]


def main():
    if not (ROOT / 'hierarchy_primitives.pdf').is_file():
        raise SystemExit('The final hierarchy_primitives.pdf must be at the package root.')
    files = [p for p in release_files() if p.name != 'SHA256SUMS']
    manifest = ''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  '
                       + p.relative_to(ROOT).as_posix() + '\n' for p in files)
    (ROOT / 'SHA256SUMS').write_text(manifest)
    files = release_files()
    target = ROOT.parent / ARCHIVE_NAME
    with zipfile.ZipFile(target, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in files:
            relative = path.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(f'{PREFIX}/{relative}', (2026, 10, 12, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(target) as archive:
        bad = archive.testzip()
        if bad is not None:
            raise SystemExit(f'Archive integrity error: {bad}')
    print(json.dumps({'archive': str(target), 'files': len(files),
                      'bytes': target.stat().st_size,
                      'sha256': hashlib.sha256(target.read_bytes()).hexdigest()}))


if __name__ == '__main__':
    main()
