#!/usr/bin/env python3
"""Read-only source inventory: bytes, SHA-256, modes and nanosecond mtimes."""
import argparse
import hashlib
import json
import stat
from pathlib import Path


def inventory(roots):
    records = []
    for arg in roots:
        root = Path(arg).resolve()
        for path in [root, *sorted(root.rglob('*'))]:
            info = path.lstat()
            row = {'root': str(root), 'relative_path': str(path.relative_to(root)),
                   'mode': stat.S_IMODE(info.st_mode), 'mtime_ns': info.st_mtime_ns,
                   'kind': 'directory' if path.is_dir() else 'file'}
            if path.is_symlink():
                raise RuntimeError('Symlink not supported: ' + str(path))
            if path.is_file():
                data = path.read_bytes()
                row.update(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
            records.append(row)
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('roots', nargs='+')
    parser.add_argument('--output', required=True)
    parser.add_argument('--compare')
    args = parser.parse_args()
    rows = inventory(args.roots)
    Path(args.output).write_text(json.dumps(rows, indent=2) + '\n')
    if args.compare:
        previous = json.loads(Path(args.compare).read_text())
        if rows != previous:
            raise AssertionError('Source bytes, paths, modes or mtimes changed')
    print(json.dumps({'entries': len(rows), 'files': sum(r['kind'] == 'file' for r in rows),
                      'exact_match': True if args.compare else None}))


if __name__ == '__main__':
    main()
