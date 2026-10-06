#!/usr/bin/env python3
"""Rebuild the complete Report170 ZIP from its fixed release manifest."""
import argparse
import hashlib
from io import BytesIO
from pathlib import Path
import sys
import zipfile
from release_tools import fresh_file, regular_bytes

ROOT = Path(__file__).absolute().parent


def release_members():
    raw = regular_bytes(ROOT / 'SHA256SUMS')
    files = {}
    for line in raw.decode('ascii').splitlines():
        digest, name = line.split('  ', 1)
        part = Path(name)
        if (len(digest) != 64 or any(c not in '0123456789abcdef' for c in digest)
                or part.is_absolute() or '..' in part.parts or '.' in part.parts
                or not name or name in files or name == 'SHA256SUMS'
                or '\\' in name):
            raise ValueError('Invalid release manifest member')
        data = regular_bytes(ROOT / part)
        if hashlib.sha256(data).hexdigest() != digest:
            raise ValueError('Release hash mismatch: ' + name)
        files[name] = data
    files['SHA256SUMS'] = raw
    return files


def build(output):
    files = release_members()
    buffer = BytesIO()
    with zipfile.ZipFile(buffer, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name, data in sorted(files.items()):
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 3, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    with fresh_file(output) as stream:
        stream.write(buffer.getvalue())
    print('Created deterministic Report170 archive with ' + str(len(files)) + ' members')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    build(parser.parse_args().output)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print('Archive build failed: ' + str(error), file=sys.stderr)
        sys.exit(1)
