#!/usr/bin/env python3
"""Create a deterministic release ZIP and SHA-256 content manifest.

Run only after rebuilding the article and completing the desired checks.
Generated Python bytecode, TeX auxiliary files and the unrelated initial
benchmark-driver schema error are excluded. Measured caps and adverse
controls remain in the archived evidence.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
NAME = 'unknot_planar_sector_overlays_20261009'
MANIFEST = 'checksums.sha256'
TEX_AUX = {'.aux', '.out', '.toc', '.fls', '.fdb_latexmk', '.synctex', '.log'}


def eligible(path: Path) -> bool:
    rel = path.relative_to(ROOT)
    if path.is_symlink():
        raise ValueError(f'release contains a symbolic link: {rel}')
    if not path.is_file() or '__pycache__' in rel.parts or path.suffix == '.pyc':
        return False
    if rel.parts[0] == 'article' and path.suffix in TEX_AUX:
        return False
    if rel.as_posix() == 'results/benchmark_driver_initial_schema_error.log':
        return False
    return rel.as_posix() != MANIFEST


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT.parent / (NAME + '.zip'))
    args = parser.parse_args()
    output = args.output.expanduser().resolve()
    if output == ROOT or ROOT in output.parents:
        parser.error('place the archive outside its source directory')
    for required in ['article/planar_sector_overlays.tex',
                     'article/planar_sector_overlays.pdf', 'integration.patch',
                     'PROVENANCE.json', 'results/full_tests.log']:
        if not (ROOT / required).is_file():
            parser.error(f'missing required artifact: {required}')
    files = sorted((p for p in ROOT.rglob('*') if eligible(p)),
                   key=lambda p: p.relative_to(ROOT).as_posix())
    records = [(hashlib.sha256(p.read_bytes()).hexdigest(),
                p.relative_to(ROOT).as_posix()) for p in files]
    (ROOT / MANIFEST).write_text(''.join(f'{digest}  {rel}\n'
                                      for digest, rel in records), encoding='utf-8')
    files = sorted(files + [ROOT / MANIFEST],
                   key=lambda p: p.relative_to(ROOT).as_posix())
    output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for path in files:
            rel = path.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(f'{NAME}/{rel}', (2026, 10, 9, 22, 3, 20))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(output) as archive:
        bad = archive.testzip()
        if bad is not None:
            raise ValueError(f'ZIP CRC check failed: {bad}')
        for digest, rel in records:
            actual = hashlib.sha256(archive.read(f'{NAME}/{rel}')).hexdigest()
            if actual != digest:
                raise ValueError(f'archived content mismatch: {rel}')
    print(f'Created {output.name}: {len(files)} files, {output.stat().st_size:,} bytes')
    print('SHA-256 ' + hashlib.sha256(output.read_bytes()).hexdigest())


if __name__ == '__main__':
    main()
