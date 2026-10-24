#!/usr/bin/env python3
"""Rebuild the delivery ZIP deterministically from the immutable release tree."""
from pathlib import Path
import argparse
import hashlib
import zipfile
from verify import authenticate

ROOT = Path(__file__).resolve().parent
PREFIX = 'ZFC_Diophantine_Budget_Interpolation'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    if output.is_relative_to(ROOT):
        raise ValueError('ZIP must be outside the immutable release tree')
    files = authenticate(ROOT)
    output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name in sorted(set(files)|{'SHA256SUMS.json'}):
            item = zipfile.ZipInfo(PREFIX+'/'+name, date_time=(2026, 10, 24, 0, 0, 0))
            item.create_system = 3
            item.external_attr = (0o100755 if name.endswith('.sh') else 0o100644) << 16
            item.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(item, (ROOT/name).read_bytes(), compresslevel=9)
    with zipfile.ZipFile(output) as archive:
        if archive.testzip() is not None:
            raise RuntimeError('New archive CRC verification failed')
    print('SHA256 '+hashlib.sha256(output.read_bytes()).hexdigest())
    print('BYTES '+str(output.stat().st_size))


if __name__ == '__main__':
    main()
