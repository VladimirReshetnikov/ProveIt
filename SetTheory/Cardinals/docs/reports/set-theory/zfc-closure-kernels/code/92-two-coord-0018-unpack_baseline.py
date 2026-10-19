#!/usr/bin/env python3
"""Extract the included, immutable 245-state reference package locally."""
import argparse
import hashlib
from pathlib import Path, PurePosixPath
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=ROOT/'work')
    args = ap.parse_args()
    archive = ROOT/'reference/zfc245-proof-20261018.zip'
    destination = args.output.resolve()
    expected_root = destination/'zfc245-proof-20261018'
    if expected_root.exists():
        ap.error('The target package already exists; choose a fresh output directory.')
    with zipfile.ZipFile(archive) as z:
        for info in z.infolist():
            p = PurePosixPath(info.filename)
            if p.is_absolute() or '..' in p.parts or p.parts[0] != expected_root.name:
                raise ValueError('Unexpected archive member: '+info.filename)
            if (info.external_attr >> 16) & 0o170000 == 0o120000:
                raise ValueError('Symbolic links are not accepted.')
        z.extractall(destination)
    # The original delivery uses its own fixed machine filenames; bind the
    # old-label table, whose name is part of the archived compiler interface.
    table = expected_root/'machine/zfc245_old.tm'
    assert hashlib.sha256(table.read_bytes()).hexdigest() == (
        'f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267')
    print(expected_root)


if __name__ == '__main__':
    main()
