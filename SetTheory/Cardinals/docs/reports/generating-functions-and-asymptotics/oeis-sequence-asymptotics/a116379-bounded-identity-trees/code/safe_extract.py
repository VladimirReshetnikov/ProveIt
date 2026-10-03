#!/usr/bin/env python3
"""Validate and extract this source archive without path traversal or symlinks."""
import argparse
from pathlib import Path, PurePosixPath
import stat
import zipfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('archive', type=Path)
parser.add_argument('destination', type=Path)
args = parser.parse_args()
if args.destination.exists():
    raise SystemExit('Destination must not already exist')
with zipfile.ZipFile(args.archive) as archive:
    members = archive.infolist()
    if len(members) > 2000 or sum(m.file_size for m in members) > 500_000_000:
        raise SystemExit('Archive exceeds size/member limit')
    names = set()
    for member in members:
        name = member.filename
        p = PurePosixPath(name)
        if not name or '\\' in name or ':' in name or p.is_absolute() or '..' in p.parts:
            raise SystemExit(f'Unsafe path: {name!r}')
        canonical = str(p)
        if canonical in names:
            raise SystemExit(f'Duplicate member: {name!r}')
        names.add(canonical)
        mode = member.external_attr >> 16
        if stat.S_ISLNK(mode) or (stat.S_IFMT(mode) not in (0, stat.S_IFREG, stat.S_IFDIR)):
            raise SystemExit(f'Unsupported member type: {name!r}')
    args.destination.mkdir(parents=True)
    for member in members:
        target = args.destination.joinpath(*PurePosixPath(member.filename).parts)
        if member.is_dir():
            target.mkdir(parents=True, exist_ok=True)
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(archive.read(member))
print(f'Extracted {len(members)} validated members to {args.destination}')
