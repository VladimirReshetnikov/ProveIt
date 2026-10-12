#!/usr/bin/env python3
"""Preview (or explicitly apply) an additive source-only ProveIt overlay."""
from __future__ import annotations
import argparse
from pathlib import Path
import shutil


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', type=Path, help='local ProveIt root')
    parser.add_argument('--apply', action='store_true', help='copy new modules, never overwrite')
    args = parser.parse_args()
    root = args.repository.resolve()
    parent = root/'Topology/UnknotRecognition/fast/fastunknot'
    source = Path(__file__).resolve().parents[1]/'src/private_cocore'
    destination = parent/'private_cocore'
    if not parent.is_dir() or not (parent/'core_primitive_annuli_verify.py').is_file():
        parser.error('expected maintained fastunknot source directory was not found')
    if destination.exists():
        parser.error('destination exists; refusing to overwrite any delivered/integrated code')
    files = sorted(source.glob('*.py'))
    for path in files:
        print(f'{path.name} -> {destination/path.name}')
    if not args.apply:
        print('Preview only. No files changed. --apply performs the additive copy.')
        return 0
    destination.mkdir()  # races/existing paths fail rather than merge
    for path in files:
        shutil.copy2(path, destination/path.name)
    print('Copied new source modules only; no native entry point or schema was changed.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
