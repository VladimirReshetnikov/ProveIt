#!/usr/bin/env python3
"""Safely integrate the rank continuation into a LOCAL pinned ProveIt checkout.

Default mode is a dry run. --apply is an explicit request to write two local
files. The canonical target must have the exact Git blob audited by the paper.
This utility never contacts GitHub, commits, pushes, or edits historical files.
"""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path
import sys

EXPECTED_BLOB = 'e61ff32263722d7575ca0202fba4dd7dad534861'
TARGET = Path('Analysis/Polylogarithms/docs/manuscript/chapters/05-signed-kernels.tex')
FRAGMENT = '05-level4-rank.tex'
ANCHOR = r'\subsection{An exact-rank conjecture in all odd weights}'


def git_blob_sha1(content: bytes) -> str:
    return hashlib.sha1(f'blob {len(content)}\0'.encode('ascii') + content).hexdigest()


def prepare(root: Path) -> tuple[Path, Path, bytes, bytes]:
    target = root.resolve() / TARGET
    source = Path(__file__).resolve().with_name(FRAGMENT)
    if not target.is_file():
        raise FileNotFoundError(f'Canonical target not found: {target}')
    original = target.read_bytes()
    actual = git_blob_sha1(original)
    if actual != EXPECTED_BLOB:
        raise ValueError(f'Refusing changed source: expected Git blob {EXPECTED_BLOB}, got {actual}. '
                         'Reconcile the new source manually; no files were written.')
    text = original.decode('utf-8')
    if text.count(ANCHOR) != 1:
        raise ValueError('Expected exactly one final rank-subsection anchor; no files were written.')
    destination = target.with_name(FRAGMENT)
    if destination.exists():
        raise FileExistsError(f'Refusing to overwrite an existing fragment: {destination}')
    # The audited subsection is the final content of this particular blob.
    before, _ = text.split(ANCHOR, 1)
    replacement = (before + r'\input{chapters/05-level4-rank}' + '\n').encode('utf-8')
    return target, destination, replacement, source.read_bytes()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repo', type=Path, help='local ProveIt repository root')
    parser.add_argument('--apply', action='store_true', help='write the verified local changes')
    args = parser.parse_args()
    try:
        target, destination, replacement, fragment = prepare(args.repo)
        if args.apply:
            # Exclusive fragment creation prevents accidental replacement.
            with destination.open('xb') as f:
                f.write(fragment)
            try:
                target.write_bytes(replacement)
            except Exception:
                destination.unlink(missing_ok=True)
                raise
            print(f'Updated {target}\nCreated {destination}')
        else:
            print(f'DRY RUN: verified Git blob {EXPECTED_BLOB}\n'
                  f'Would replace the final rank subsection in {target}\n'
                  f'Would create {destination}\nNo files were written.')
        print('Review the diff, add the research report and receipts, then rebuild the manuscript locally.')
        return 0
    except (OSError, ValueError, UnicodeError) as exc:
        print(f'Integration stopped: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
