#!/usr/bin/env python3
"""Build a deterministic Git-compatible integration patch from bundled trees."""
from __future__ import annotations
import argparse
import difflib
import hashlib
from pathlib import Path

BUNDLE = Path(__file__).resolve().parents[1]
PREFIX = 'Topology/UnknotRecognition/fast/'


def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def files(root):
    return {p.relative_to(root).as_posix(): p for p in root.rglob('*')
            if p.is_file() and '__pycache__' not in p.parts and p.suffix != '.pyc'}


def make_patch():
    old = files(BUNDLE / 'baseline/fast')
    new = files(BUNDLE / 'implementation/fast')
    chunks = []
    changed = []
    for name in sorted(old.keys() | new.keys()):
        before = old[name].read_bytes() if name in old else None
        after = new[name].read_bytes() if name in new else None
        if before == after:
            continue
        changed.append(name)
        a, b = 'a/' + PREFIX + name, 'b/' + PREFIX + name
        chunks.append(f'diff --git {a} {b}\n')
        if before is None:
            chunks.append('new file mode 100644\n')
        elif after is None:
            chunks.append('deleted file mode 100644\n')
        ah = blob(before) if before is not None else '0' * 40
        bh = blob(after) if after is not None else '0' * 40
        chunks.append(f'index {ah}..{bh}' + (' 100644' if before is not None and after is not None else '') + '\n')
        lines = difflib.unified_diff(
            (before or b'').decode('utf-8').splitlines(keepends=True),
            (after or b'').decode('utf-8').splitlines(keepends=True),
            fromfile=a if before is not None else '/dev/null',
            tofile=b if after is not None else '/dev/null', n=3)
        for line in lines:
            chunks.append(line if line.endswith('\n') else line + '\n\\ No newline at end of file\n')
    return ''.join(chunks), changed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=BUNDLE / 'patches/fast_dense_algebra_and_a5.patch')
    args = parser.parse_args()
    patch, changed = make_patch()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(patch)
    print(f'Wrote {len(changed)} changed/new files to {args.output}')


if __name__ == '__main__':
    main()
