#!/usr/bin/env python3
"""Reconstruct FM215 from the pinned literal primary K215 table."""
from pathlib import Path
import argparse
import hashlib
import json
from verify_fm215 import HERE, PARENT_SHA, NEW_SHA, DENSE_SHA, PATCH, parse, sha


def encode(table, mapping=None):
    out = ['#! start 0']
    for (q, b), (w, d, n) in sorted(table.items()):
        if mapping is not None:
            q, n = mapping[q], mapping[n]
        out.append(f'{q} {b} {w} {"R" if d == 1 else "L"} {n}')
    return ('\n'.join(out) + '\n').encode()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', required=True, type=Path)
    args = ap.parse_args()
    source = HERE / 'tables/00.tm'
    assert sha(source) == PARENT_SHA
    table, start = parse(source)
    assert start == 0
    table.update(PATCH)
    states = sorted({q for q, b in table})
    assert len(states) == 215
    mapping = {q: i for i, q in enumerate(states)}
    mapping[254] = 215
    native, dense = encode(table), encode(table, mapping)
    assert hashlib.sha256(native).hexdigest() == NEW_SHA
    assert hashlib.sha256(dense).hexdigest() == DENSE_SHA
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / 'fm215.native.tm').write_bytes(native)
    (args.output / 'fm215.tm').write_bytes(dense)
    (args.output / 'canonicalization.json').write_text(json.dumps({
        'native_to_dense': mapping, 'start': 0, 'dispatcher': mapping[84],
        'halt': 215}, indent=2) + '\n')
    print(json.dumps({'native_sha256': NEW_SHA, 'dense_sha256': DENSE_SHA,
                      'states': 215, 'changed_rows': len(PATCH)}, indent=2))


if __name__ == '__main__':
    main()
