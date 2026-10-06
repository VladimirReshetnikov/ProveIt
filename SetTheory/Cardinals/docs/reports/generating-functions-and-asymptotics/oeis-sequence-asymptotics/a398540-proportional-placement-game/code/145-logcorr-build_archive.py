#!/usr/bin/env python3
"""Create a deterministic, allowlisted Report145 archive without overwriting."""
import argparse
import hashlib
import io
import os
from pathlib import Path
import stat
import sys
import zipfile

FILES = (
    'README.md', 'Report145.pdf', 'Report145.tex', 'build_archive.py', 'build_pdf.py',
    'companion/README.md', 'companion/checks.py', 'companion/fixture.json',
    'companion/receipt.json', 'companion/test_checks.py',
    'companion/tests-normal.json', 'companion/tests-optimized.json',
    'foundation/Report144.pdf', 'foundation/Report144.tex', 'toolchain.json',
)


def exclusive_output(path, data):
    raw = os.fspath(path)
    if not raw or '\x00' in raw or raw.endswith(os.sep) or '..' in Path(raw).parts:
        raise ValueError('invalid output path')
    absolute = Path(os.path.abspath(raw))
    parts = absolute.parts
    fd = os.open(parts[0], os.O_RDONLY | os.O_DIRECTORY)
    try:
        for component in parts[1:-1]:
            new = os.open(component, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = new
        target = os.open(parts[-1], os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600, dir_fd=fd)
        with os.fdopen(target, 'wb') as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
    finally:
        os.close(fd)


def archive_bytes(root):
    payload = {}
    for name in sorted(FILES):
        path = root / name
        if any(part.is_symlink() for part in [path] + list(path.parents)):
            raise ValueError('symlink input refused: ' + name)
        if not stat.S_ISREG(path.stat().st_mode):
            raise ValueError('non-regular input refused: ' + name)
        payload[name] = path.read_bytes()
    payload['SHA256SUMS'] = ''.join(hashlib.sha256(payload[name]).hexdigest() + '  ' + name + '\n' for name in sorted(payload)).encode('ascii')
    stream = io.BytesIO()
    with zipfile.ZipFile(stream, 'w', compression=zipfile.ZIP_STORED, allowZip64=False) as archive:
        for name in sorted(payload):
            item = zipfile.ZipInfo('Report145/' + name, date_time=(2026, 10, 3, 0, 0, 0))
            item.compress_type = zipfile.ZIP_STORED
            item.create_system = 3
            item.external_attr = (stat.S_IFREG | 0o644) << 16
            item.extra = b''
            item.comment = b''
            archive.writestr(item, payload[name])
    return stream.getvalue()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, help='new ZIP path, with existing nonsymlink parent directories')
    args = parser.parse_args()
    data = archive_bytes(Path(__file__).resolve().parent)
    exclusive_output(args.output, data)
    print(hashlib.sha256(data).hexdigest() + '  Report145.zip')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print('Archive failed: ' + str(error), file=sys.stderr)
        sys.exit(1)
