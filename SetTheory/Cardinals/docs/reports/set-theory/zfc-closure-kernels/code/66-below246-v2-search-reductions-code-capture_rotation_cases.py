#!/usr/bin/env python3
"""Create finite fixtures for a new parenthesization of the same ordered leaves.

This checker imports only parsing, tape painting, and instruction semantics
from the pinned context246 package. It does not simulate an unverified table
to decide the expected result. The fixture ordering places four known partial
decoder failures first. All values are concrete witnesses, not reachability
claims.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline', type=Path, required=True)
    ap.add_argument('--logical-sites', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--frontier', type=int,
                    help='Place 24 fixtures beginning at this reordered index first')
    args = ap.parse_args()
    assert __debug__, 'Assertions must be enabled.'
    sys.path.insert(0, str(args.baseline.resolve() / 'code'))
    import check_literal_instructions as p
    sites = json.loads(args.logical_sites.read_text())
    source = args.baseline / 'sources/Prog254.v'
    old = p.program_sites(source)
    assert [(op, r) for pc, op, r in old] == [(op, r) for pc, op, r in sites]
    rows, metadata = [], []
    for index, (pc, op, reg) in enumerate(sites):
        for positive in ((False, True) if op == 'CD' else (None,)):
            values = [3 * i % 7 for i in range(9)]
            if op == 'CD': values[p.PHYSICAL[reg]] = 1 if positive else 0
            ones = p.paint(pc, 40, values, [0], 0)
            target = p.expected(pc, op, reg, values, [0], 0, 40)
            state, head, final = (96, target[0], target[1]) if target else (254, 0, set())
            rows.append((96, 0, len(ones), *sorted(ones), state, head,
                         len(final), *sorted(final)))
            metadata.append(dict(index=index, pc=pc, op=op, r=reg,
                                 positive=positive, regs=values))
    critical_paths = {'11101001001010100010110000',
                      '11101001001010100111000000'}
    critical = [i for i, m in enumerate(metadata) if m['pc'] in critical_paths]
    assert critical == [707, 708, 1166, 1167]
    order = critical + [i for i in range(len(rows)) if i not in critical]
    rows, metadata = [rows[i] for i in order], [metadata[i] for i in order]
    name = 'rotation'
    if args.frontier is not None:
        start = args.frontier
        front = list(range(start, min(start + 24, len(rows))))
        order = front + [i for i in range(len(rows)) if i not in front]
        rows, metadata = [rows[i] for i in order], [metadata[i] for i in order]
        name = f'near{start}'
    out = args.output
    out.mkdir(parents=True, exist_ok=True)
    (out / f'{name}-fixtures.txt').write_text(str(len(rows)) + '\n' + '\n'.join(
        ' '.join(map(str, row)) for row in rows) + '\n')
    (out / f'{name}-fixtures.json').write_text(json.dumps(metadata, indent=2) + '\n')
    (out / f'{name}-fixture-order.json').write_text(json.dumps(order) + '\n')
    result = dict(status='PASS', scope='Finite, independently specified instruction fixtures',
                  cases=len(rows), original_ordered_leaves_preserved=True,
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  logical_sites_sha256=hashlib.sha256(args.logical_sites.read_bytes()).hexdigest(),
                  selected_values='physical i has (3*i)%7; CD selected value 0 or 1',
                  spare_values=[0], head=0, header_distance=40)
    (out / f'{name}-fixture-summary.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
