#!/usr/bin/env python3
"""Verify the frozen Report162 allowlist and create a reproducible stored ZIP."""
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
    'README.md',
    'Report162.pdf',
    'Report162.tex',
    'SOURCE_PROVENANCE.json',
    'build_pdf.py',
    'companion/README.md',
    'companion/prefactor.py',
    'companion/test_prefactor.py',
    'data/counts.json',
    'data/finite_checks.json',
    'data/illustrations.json',
    'data/series_counts.json',
    'make_zip.py',
    'release_tools.py',
    'test_release.py',
)
MAX_PAYLOAD_BYTES = 64 * 1024 * 1024
MAX_MEMBERS = 64


def collect(root):
    root = Path(root)
    raw = regular_bytes(root / 'SHA256SUMS', 65536)
    recorded = {}
    for line in raw.decode('ascii').splitlines():
        found = re.fullmatch(r'([0-9a-f]{64})  ([A-Za-z0-9_./-]+)', line)
        if not found:
            raise ValueError('Malformed checksum line')
        digest, name = found.groups()
        if name in recorded:
            raise ValueError('Duplicate checksum member')
        recorded[name] = digest
    if list(recorded) != sorted(FILES):
        raise ValueError('Manifest does not match the sorted fixed allowlist')
    payload = {}
    for name in sorted(FILES):
        data = regular_bytes(root / name)
        if hashlib.sha256(data).hexdigest() != recorded[name]:
            raise ValueError('Checksum mismatch: ' + name)
        payload[name] = data
    payload['SHA256SUMS'] = raw
    if sum(map(len, payload.values())) > MAX_PAYLOAD_BYTES:
        raise ValueError('Payload exceeds 64 MiB')
    return payload


def archive_bytes(payload):
    if type(payload) is not dict or not 1 <= len(payload) <= MAX_MEMBERS:
        raise ValueError('Payload must be a dictionary of 1 to 64 members')
    total = 0
    for name, content in payload.items():
        if type(name) is not str or len(name) > 200 or re.fullmatch(r'[A-Za-z0-9_./-]+', name) is None:
            raise ValueError('Invalid archive member name')
        if any(part in ('', '.', '..') for part in name.split('/')):
            raise ValueError('Unsafe archive member path')
        if type(content) is not bytes or len(content) > 16 * 1024 * 1024:
            raise ValueError('Each member must be bytes of at most 16 MiB')
        total += len(content)
    if total > MAX_PAYLOAD_BYTES:
        raise ValueError('Payload exceeds 64 MiB')
    stream = io.BytesIO()
    with zipfile.ZipFile(stream, 'w', compression=zipfile.ZIP_STORED) as archive:
        for name in sorted(payload):
            member = zipfile.ZipInfo(name, date_time=(2026, 10, 3, 0, 0, 0))
            member.create_system = 3
            member.external_attr = (stat.S_IFREG | 0o644) << 16
            member.compress_type = zipfile.ZIP_STORED
            archive.writestr(member, payload[name])
    result = stream.getvalue()
    with zipfile.ZipFile(io.BytesIO(result)) as archive:
        if archive.namelist() != sorted(payload) or archive.testzip() is not None:
            raise RuntimeError('Archive verification failed')
        for name, data in payload.items():
            if archive.read(name) != data:
                raise RuntimeError('Archive bytes mismatch')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    payload = collect(Path(__file__).absolute().parent)
    result = archive_bytes(payload)
    with fresh_file(args.output) as output:
        output.write(result)
    print(hashlib.sha256(result).hexdigest() + '  ' + Path(args.output).name)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, RuntimeError, UnicodeError, zipfile.BadZipFile) as error:
        print('Archive failed: ' + str(error), file=sys.stderr)
        sys.exit(1)
