#!/usr/bin/env python3
"""Safely unpack this research ZIP into a new directory.
Usage: python safe_extract.py archive.zip new_destination
"""
from pathlib import Path, PurePosixPath
import argparse
import shutil
import stat
import zipfile


def extract(archive, destination):
    destination = Path(destination).resolve()
    if destination.exists():
        raise ValueError('destination must not already exist')
    with zipfile.ZipFile(archive) as bundle:
        entries = bundle.infolist()
        if len(entries) > 10000 or sum(info.file_size for info in entries) > 100_000_000:
            raise ValueError('archive exceeds the research-package safety limits')
        seen = set()
        for info in entries:
            name = info.filename
            path = PurePosixPath(name)
            if (not name or '\\' in name or path.is_absolute() or '..' in path.parts
                    or ':' in path.parts[0] or name in seen):
                raise ValueError('unsafe or duplicate archive member: ' + repr(name))
            seen.add(name)
            kind = stat.S_IFMT(info.external_attr >> 16)
            if kind not in (0, stat.S_IFREG, stat.S_IFDIR):
                raise ValueError('links and special archive members are not supported')
            target = destination.joinpath(*path.parts)
            if not target.resolve().is_relative_to(destination):
                raise ValueError('archive member escapes destination')
        destination.mkdir(parents=True)
        for info in entries:
            target = destination.joinpath(*PurePosixPath(info.filename).parts)
            if info.is_dir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                with bundle.open(info) as source, target.open('xb') as output:
                    shutil.copyfileobj(source, output)
    print('Safely extracted', len(entries), 'members to', destination)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('archive')
    parser.add_argument('destination')
    args = parser.parse_args()
    extract(args.archive, args.destination)
