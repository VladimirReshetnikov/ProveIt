#!/usr/bin/env python3
"""Check delivered file identity; this is not a mathematical proof checker."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = ap.parse_args()
    root = args.root.resolve()
    data = json.loads((root/'MANIFEST.json').read_text())
    total = 0
    for item in data['files']:
        relative = PurePosixPath(item['path'])
        if relative.is_absolute() or '..' in relative.parts:
            raise ValueError('Unsafe manifest member')
        path = root.joinpath(*relative.parts)
        if not path.is_file() or path.is_symlink():
            raise ValueError('Missing regular file: '+str(relative))
        raw = path.read_bytes()
        if len(raw) != item['bytes'] or hashlib.sha256(raw).hexdigest() != item['sha256']:
            raise ValueError('Identity mismatch: '+str(relative))
        total += len(raw)
    print(json.dumps(dict(status='PASS_FILE_IDENTITIES', files=len(data['files']), bytes=total,
                          mathematical_correctness_asserted=False), indent=2))


if __name__ == '__main__':
    main()
