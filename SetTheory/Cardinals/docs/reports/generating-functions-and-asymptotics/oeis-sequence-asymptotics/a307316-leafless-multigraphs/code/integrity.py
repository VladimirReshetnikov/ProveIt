#!/usr/bin/env python3
"""Create or verify the closed, bytewise package inventory (standard library)."""
import sys
sys.dont_write_bytecode=True
import argparse
import hashlib
from pathlib import Path
import re
import sys

INVENTORY = 'CHECKSUMS.sha256'
class IntegrityError(ValueError):
    pass

def require(condition, message):
    if not condition:
        raise IntegrityError(message)

def files(root):
    result = {}
    for p in sorted(root.rglob('*')):
        require(not p.is_symlink(), 'SYMLINK: ' + p.relative_to(root).as_posix())
        if p.is_file() and p.relative_to(root).as_posix() != INVENTORY:
            rel = p.relative_to(root).as_posix()
            require('\n' not in rel and '\r' not in rel, 'INVALID_PATH')
            result[rel] = hashlib.sha256(p.read_bytes()).hexdigest()
        else:
            require(p.is_dir() or (p.relative_to(root).as_posix() == INVENTORY and p.is_file()), 'NONREGULAR_FILE')
    return result

def check(root):
    root = Path(root).resolve()
    inventory = root / INVENTORY
    require(inventory.is_file() and not inventory.is_symlink(), 'MISSING_INVENTORY')
    expected = {}
    for line in inventory.read_text(encoding='utf-8').splitlines():
        match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        require(match is not None, 'INVALID_INVENTORY_LINE')
        digest, rel = match.groups()
        parts = rel.split('/')
        require(not rel.startswith('/') and all(x not in ('', '.', '..') for x in parts)
                and '\\' not in rel and rel != INVENTORY, 'UNSAFE_INVENTORY_PATH')
        require(rel not in expected, 'DUPLICATE_INVENTORY_PATH')
        expected[rel] = digest
    require(bool(expected), 'EMPTY_INVENTORY')
    require(list(expected) == sorted(expected), 'UNSORTED_INVENTORY')
    actual = files(root)
    expected_dirs = {parent.as_posix() for rel in expected
                     for parent in Path(rel).parents if parent.as_posix() != '.'}
    actual_dirs = {path.relative_to(root).as_posix() for path in root.rglob('*') if path.is_dir()}
    missing = sorted(set(expected) - set(actual))
    extra = sorted(set(actual) - set(expected))
    require(not missing, 'MISSING_FILE: ' + ', '.join(missing))
    require(not extra, 'UNEXPECTED_FILE: ' + ', '.join(extra))
    require(actual_dirs == expected_dirs, 'UNEXPECTED_DIRECTORY: ' + ', '.join(sorted(actual_dirs - expected_dirs)))
    changed = [p for p in expected if expected[p] != actual[p]]
    require(not changed, 'HASH_MISMATCH: ' + ', '.join(changed))
    return len(expected)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('root', nargs='?', type=Path, default=Path(__file__).resolve().parent)
    ap.add_argument('--write', action='store_true', help='replace inventory for deliberate author-side repackaging')
    args = ap.parse_args()
    root = args.root.resolve()
    try:
        if args.write:
            inventory = files(root)
            (root / INVENTORY).write_text(''.join(f'{digest}  {p}\n' for p, digest in inventory.items()), encoding='utf-8')
        count = check(root)
        print(f'PACKAGE_INTEGRITY_PASS {count} files')
    except (IntegrityError, OSError, UnicodeError) as exc:
        print('PACKAGE_INTEGRITY_FAIL ' + str(exc), file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
