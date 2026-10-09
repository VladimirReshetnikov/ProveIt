#!/usr/bin/env python3
"""Preview (default) or apply the localized Goncharov-simplex order correction.

Only the exact reviewed Git blob is accepted. The script does not connect to
GitHub, create commits, or revise unsupported mathematical claims automatically.
On a different revision, stop and reconcile the source rather than bypassing
this guard. A successful --write creates a .before-order-fix backup first.
"""
from __future__ import annotations
import argparse
import difflib
import hashlib
from pathlib import Path
import sys

RELATIVE = Path('Analysis/Polylogarithms/docs/articles/gaussian-eisenstein-double-polylogs.tex')
EXPECTED_BLOB = '8aee642511b3f1ad791c245c34ad032d3fe4be83'
OLD = r'\int_{0<t_1<\dots<t_n<1}'
NEW = r'\int_{0<t_n<\dots<t_1<1}'


def git_blob_sha(data: bytes) -> str:
    return hashlib.sha1(b'blob '+str(len(data)).encode('ascii')+b'\0'+data).hexdigest()


def transform(text: str) -> str:
    if text.count(OLD) != 1:
        raise ValueError('Expected exactly one matching simplex; no changes made.')
    if r'\label{eq:G-def}' not in text:
        raise ValueError('Expected equation label is absent; no changes made.')
    return text.replace(OLD, NEW, 1)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', type=Path, help='Local ProveIt repository root')
    parser.add_argument('--write', action='store_true', help='Apply after hash validation; otherwise preview only')
    args = parser.parse_args()
    target = args.repository/RELATIVE
    try:
        raw = target.read_bytes()
        observed = git_blob_sha(raw)
        if observed != EXPECTED_BLOB:
            raise ValueError(f'Revision mismatch: expected {EXPECTED_BLOB}, observed {observed}. No changes made.')
        before = raw.decode('utf-8')
        after = transform(before)
        diff = ''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),
                                          fromfile='a/'+str(RELATIVE),tofile='b/'+str(RELATIVE)))
        sys.stdout.write(diff)
        if args.write:
            backup = target.with_name(target.name+'.before-order-fix')
            # Exclusive backup creation avoids silently replacing an older backup.
            with backup.open('xb') as f:
                f.write(raw)
            target.write_bytes(after.encode('utf-8'))
            print(f'Applied one localized replacement. Backup: {backup}', file=sys.stderr)
        else:
            print('Preview only; original file unchanged.', file=sys.stderr)
        return 0
    except (OSError, UnicodeError, ValueError) as exc:
        print(str(exc),file=sys.stderr)
        return 2

if __name__ == '__main__':
    raise SystemExit(main())
