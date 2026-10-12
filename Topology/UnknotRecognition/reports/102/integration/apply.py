#!/usr/bin/env python3
"""Hash-guarded integration proposal. Default: check only, never modify.

Usage: python integration/apply.py /path/to/ProveIt [--write]

The real pinned checkout was not available in this delivery's runtime. The
transformations and verifier helper were tested on explicit patch fixtures.
The tool refuses changed source blobs; review/port rather than bypass the pin.
"""
import argparse
import hashlib
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREFIX = Path('Topology/UnknotRecognition/fast/fastunknot')
BASE = {
    'core_handlebody.py': '13935f9cfa9ecf70fa5966a2ceec58f0f3167ff7',
    'bundle_boundary_kernel.py': '8caf8a7387d4b4532f43e45707ba18d57626625a',
    'core_handlebody_verify.py': '9819307acca29c06789bb986a978c6eed0c83b36',
}


def git_blob(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()


def once(text, before, after):
    if text.count(before) != 1:
        raise ValueError('patch target is missing or ambiguous')
    return text.replace(before, after, 1)


def transform(name, text):
    if name == 'core_handlebody.py':
        text = once(text, 'from heapq import heappop, heappush\n',
                    'from heapq import heappop, heappush\n\nfrom .column_cancellation import column_cancellation_plan\n')
        return once(text, 'planned = capped_cancellation_plan(counts, check=check)',
                    'planned = column_cancellation_plan(counts, check=check)')
    if name == 'bundle_boundary_kernel.py':
        text = once(text, 'from collections import Counter\n',
                    'from collections import Counter\n\nfrom .column_cancellation import column_cancellation_plan\n')
        return once(text, 'planned = capped_cancellation_plan(rows, check=check)',
                    'planned = column_cancellation_plan(rows, check=check)')
    if name == 'core_handlebody_verify.py':
        text = once(text, 'from .integer_codec import certificate_equal\n',
                    'from .integer_codec import certificate_equal\nfrom .column_cancellation_verify import private_column_schedule\n')
        old = ('    else:\n'
               '        matrix = [[row.get(c, 0) for c in range(m)] for row in matrix]\n')
        new = ('    elif private_column_schedule(matrix, moves, live_columns, check=check):\n'
               '        # Source counts are authenticated above. No active fill occurs.\n'
               '        for r, c in moves:\n'
               '            live_rows.remove(r)\n'
               '            live_columns.remove(c)\n'
               '        moves = []\n'
               '    else:\n'
               '        matrix = [[row.get(c, 0) for c in range(m)] for row in matrix]\n')
        return once(text, old, new)
    raise ValueError('unknown target')


def prepare(root):
    changes = {}
    for name, expected in BASE.items():
        path = root/PREFIX/name
        raw = path.read_bytes()
        # Git normally stores LF; do not silently normalize an altered checkout.
        if git_blob(raw) != expected:
            raise ValueError(f'{name}: pinned Git blob does not match; no files changed')
        modified = transform(name, raw.decode('utf-8'))
        compile(modified, str(path), 'exec')
        changes[path] = modified.encode('utf-8')
    additions = {
        'column_cancellation.py': HERE.parent/'cancellation'/'peeling.py',
        'column_cancellation_verify.py': HERE/'column_cancellation_verify.py',
    }
    for name, source in additions.items():
        path = root/PREFIX/name
        if path.exists():
            raise ValueError(f'{name} already exists; no files changed')
        changes[path] = source.read_bytes()
        compile(changes[path], str(path), 'exec')
    return changes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', type=Path)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    changes = prepare(args.repository)
    for path, contents in changes.items():
        print(('WRITE ' if args.write else 'CHECK ')+str(path))
    if args.write:
        # Prepare all bytes before replacing any target. Existing files get
        # byte-for-byte backups. This is not a multi-file transactional system.
        for path, contents in changes.items():
            backup = path.with_name(path.name+'.before-column-cancellation')
            if path.exists() and backup.exists():
                raise ValueError(f'backup already exists: {backup}; no files changed')
        for path, contents in changes.items():
            if path.exists():
                path.with_name(path.name+'.before-column-cancellation').write_bytes(path.read_bytes())
            temp = path.with_name(path.name+'.column-cancellation-tmp')
            temp.write_bytes(contents)
            os.replace(temp, path)
    print('Prepared producer replacements and core-verifier fast path.'
          ' The whole-cut boundary verifier is intentionally unchanged.')


if __name__ == '__main__':
    main()
