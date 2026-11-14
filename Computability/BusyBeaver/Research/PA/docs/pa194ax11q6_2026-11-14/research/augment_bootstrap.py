#!/usr/bin/env python3
"""Union source contexts with every window of an exact blank bootstrap.

The endpoint after the last transition is included. Only controls already
represented by the source collector are narrowed; arithmetic-box controls
remain covered by the searcher's original abstract invariant.
"""
from pathlib import Path
import argparse
import json
from audit_support import read_table, read_contexts, write_contexts, sha256


def augment(table, source, steps, radius=6, start=74):
    rows, states, halt = read_table(table)
    original = read_contexts(source, radius)
    narrowed = {q for q, _ in original}
    assert narrowed <= states and start in states
    union = set(original)
    ones = set()
    q, head = start, 0
    for t in range(steps + 1):
        assert q in states, ('early halt', t, q)
        if q in narrowed:
            pattern = sum(int(head + i in ones) << (i + radius)
                          for i in range(-radius, radius + 1))
            union.add((q, pattern))
        if t == steps:
            break
        b = int(head in ones)
        w, d, n = rows[q, b]
        if w:
            ones.add(head)
        else:
            ones.discard(head)
        q, head = n, head + d
    receipt = {
        'status': 'PASS', 'table_sha256': sha256(table),
        'source_contexts_sha256': sha256(source), 'radius': radius,
        'start': start, 'blank': 0, 'transitions': steps,
        'includes_final_endpoint': True,
        'source_contexts': len(original), 'augmented_contexts': len(union),
        'added_contexts': len(union - original),
        'narrowed_controls': len(narrowed),
        'endpoint': {'state': q, 'head': head, 'ones': sorted(ones)},
        'scope': 'Exact finite bootstrap windows unioned with the supplied source envelope. No inference of unbounded behavior from this prefix.'
    }
    return union, receipt


def main():
    if not __debug__:
        raise SystemExit('Do not use Python -O: assertions are verification checks.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table', type=Path)
    ap.add_argument('source_contexts', type=Path)
    ap.add_argument('output', type=Path)
    ap.add_argument('--steps', type=int, required=True)
    ap.add_argument('--radius', type=int, default=6)
    ap.add_argument('--start', type=int, default=74)
    args = ap.parse_args()
    pairs, receipt = augment(args.table, args.source_contexts, args.steps,
                             args.radius, args.start)
    write_contexts(args.output, pairs)
    receipt['augmented_contexts_sha256'] = sha256(args.output)
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
