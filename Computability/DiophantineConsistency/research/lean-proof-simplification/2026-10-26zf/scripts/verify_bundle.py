#!/usr/bin/env python3
"""Verify final bundle members against MANIFEST.sha256; no network or mutation."""
import hashlib
import json
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1]
    manifest = root / 'MANIFEST.sha256'
    expected = {}
    problems = []
    for line in manifest.read_text(encoding='utf-8').splitlines():
        digest, name = line.split('  ', 1)
        target = (root / name).resolve()
        if not target.is_relative_to(root) or name in expected:
            problems.append('invalid or duplicate manifest path: ' + name)
            continue
        expected[name] = digest
        if not target.is_file():
            problems.append('missing: ' + name)
        elif hashlib.sha256(target.read_bytes()).hexdigest() != digest:
            problems.append('hash mismatch: ' + name)
    actual = {p.relative_to(root).as_posix() for p in root.rglob('*')
              if p.is_file() and p != manifest and '__pycache__' not in p.parts}
    unexpected = sorted(actual - set(expected))
    print(json.dumps({'status': 'passed' if not problems else 'failed',
                      'manifest_members': len(expected), 'problems': problems,
                      'additional_local_files': unexpected}, indent=2))
    return 1 if problems else 0


if __name__ == '__main__':
    raise SystemExit(main())
