#!/usr/bin/env python3
"""Verify and archive the exact Report149 release allowlist deterministically."""
import argparse
import hashlib
import io
from pathlib import Path
import re
import stat
import sys
import zipfile
from release_tools import fresh_file, regular_bytes

FILES = (
    'README.md', 'Report149.tex', 'Report149.pdf', 'SOURCE_PROVENANCE.json',
    'build_pdf.py', 'make_zip.py', 'release_tools.py', 'test_release.py',
    'companion/README.md', 'companion/exact.py', 'companion/permutations.py',
    'companion/verify.py', 'companion/safeio.py', 'companion/evidence.json',
    'companion/tests/test_companion.py',
)
STAMP = (2026, 10, 3, 0, 0, 0)


def collect(root):
    root = Path(root)
    manifest_bytes = regular_bytes(root / 'SHA256SUMS')
    manifest = {}
    for line in manifest_bytes.decode('ascii').splitlines():
        match = re.fullmatch(r'([0-9a-f]{64})  ([A-Za-z0-9_./-]+)', line)
        if match is None:
            raise ValueError('Malformed checksum line')
        digest, name = match.groups()
        if name in manifest:
            raise ValueError('Duplicate checksum member')
        manifest[name] = digest
    if tuple(manifest) != tuple(sorted(FILES)):
        raise ValueError('Checksum members differ from the fixed sorted allowlist')
    payload = {}
    for name in sorted(FILES):
        content = regular_bytes(root / name)
        if hashlib.sha256(content).hexdigest() != manifest[name]:
            raise ValueError('Checksum mismatch: ' + name)
        payload[name] = content
    payload['SHA256SUMS'] = manifest_bytes
    return payload


def archive_bytes(payload):
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, mode='w', compression=zipfile.ZIP_STORED) as archive:
        for name, data in sorted(payload.items()):
            item = zipfile.ZipInfo(name, date_time=STAMP)
            item.create_system = 3
            item.external_attr = (stat.S_IFREG | 0o644) << 16
            item.compress_type = zipfile.ZIP_STORED
            archive.writestr(item, data)
    content = buffer.getvalue()
    with zipfile.ZipFile(io.BytesIO(content)) as check:
        if check.namelist() != sorted(payload) or check.testzip() is not None:
            raise RuntimeError('ZIP verification failed')
        for name, data in payload.items():
            if check.read(name) != data:
                raise RuntimeError('ZIP content mismatch: ' + name)
    return content


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    payload = collect(Path(__file__).absolute().parent)
    zipped = archive_bytes(payload)
    with fresh_file(args.output) as output:
        output.write(zipped)
    print(hashlib.sha256(zipped).hexdigest() + '  ' + Path(args.output).name)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, RuntimeError, UnicodeError, zipfile.BadZipFile) as problem:
        print('Archive build failed: ' + str(problem), file=sys.stderr)
        sys.exit(1)
