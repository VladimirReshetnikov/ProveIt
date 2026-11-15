#!/usr/bin/env python3
"""Construct PA194SEL by two simultaneous history-selector rewrites.

No search, external package, network, or proof assistant is required.
The independent checker is verification/check.py.
"""
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent
PRIMARY_HASH = '4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f'
PAIRS = [(12, 38, 98, 19), (127, 124, 8, 59)]


def parse(data):
    table = {}
    for line in data.decode('ascii').splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        if (q, b) in table or b not in (0, 1) or w not in (0, 1) or d not in ('L', 'R'):
            raise ValueError('Bad row')
        table[q, b] = (w, d, n)
    return table


def encode(rows):
    return ''.join(f'{q} {b} {w} {d} {n}\n' for (q, b), (w, d, n) in sorted(rows.items())).encode()


def dense(rows):
    labels, index = [74], {74: 0}
    for q in labels:
        for b in (0, 1):
            n = rows[q, b][2]
            if n != 254 and n not in index:
                index[n] = len(labels)
                labels.append(n)
    if len(labels) != 194 or set(labels) != {q for q, b in rows}:
        raise ValueError('Not a spanning 194-state table')
    index[254] = 194
    return {(index[q], b): (w, d, index[n]) for (q, b), (w, d, n) in rows.items()}, labels + [254]


def build(out):
    data = (HERE / 'inputs/primary.tm').read_bytes()
    if hashlib.sha256(data).hexdigest() != PRIMARY_HASH:
        raise ValueError('Primary identity mismatch')
    base = parse(data)
    old_labels = json.loads((HERE / 'inputs/primary.labels.json').read_text())
    native = {(old_labels[q], b): (w, d, old_labels[n]) for (q, b), (w, d, n) in base.items()}
    if encode(native) != (HERE / 'inputs/primary.native.tm').read_bytes():
        raise ValueError('Native input is not the pinned dense input')
    alias = {b: a for a, b, p0, p1 in PAIRS}
    rho = lambda q: alias.get(q, q)
    child = {(q, b): (w, d, rho(n)) for (q, b), (w, d, n) in native.items()}
    for keep, selector, p0, p1 in PAIRS:
        if native[keep, 1] != native[selector, 1]:
            raise ValueError('Common branch differs')
        child[keep, 0] = (0, 'L', selector)
        child[selector, 0] = (0, 'R', p0)
        child[selector, 1] = (1, 'R', p1)
    table, labels = dense(child)
    out.mkdir(parents=True, exist_ok=True)
    (out / 'pa194sel.tm').write_bytes(encode(table))
    (out / 'pa194sel.native.tm').write_bytes(encode(child))
    (out / 'pa194sel.labels.json').write_text(json.dumps(labels) + '\n')
    changes = [{'state': q, 'read': b, 'old': list(native[q, b]), 'new': list(child[q, b])}
               for q, b in sorted(native) if native[q, b] != child[q, b]]
    result = dict(name='PA194SEL', working_states=194, rows=388, start=0, halt=194,
                  native_start=74, native_halt=254, pairs=PAIRS, changed_native_rows=changes,
                  dense_sha256=hashlib.sha256(encode(table)).hexdigest(),
                  native_sha256=hashlib.sha256(encode(child)).hexdigest(),
                  local_time_factors=[1, 3], proof_scope='Direct relative finite-run preservation; absolute iPRA calibration of the primary remains separate')
    (out / 'construction.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=HERE / 'machine')
    build(ap.parse_args().output)
