#!/usr/bin/env python3
"""Capture an exact bounded literal trace of a failed rotation-control fixture."""
import argparse
import hashlib
import json
from pathlib import Path
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline', type=Path, required=True)
    ap.add_argument('--table', type=Path, required=True)
    ap.add_argument('--fixtures', type=Path, required=True)
    ap.add_argument('--fixture', type=int, default=7651)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    assert __debug__
    sys.path.insert(0, str(args.baseline.resolve() / 'code'))
    import check_literal_instructions as p
    table = p.read_table(args.table)
    case = json.loads(args.fixtures.read_text())[args.fixture]
    pc, op, reg, values = case['pc'], case['op'], case['r'], case['regs']
    target = p.expected(pc, op, reg, values, [0], 0, 40)
    assert target is not None
    ones = p.paint(pc, 40, values, [0], 0)
    state, head, trace, visits = 96, 0, [], []
    outcome = 'fuel_bound'
    for tick in range(10000):
        read = int(head in ones)
        write, direction, following = table[state, read]
        trace.append([tick, state, head, read, write, direction, following])
        state = following
        if write: ones.add(head)
        else: ones.discard(head)
        head += direction
        if state == 254:
            outcome = 'unexpected_halt'
            break
        if state == 96:
            visits.append(dict(step=tick+1, head=head,
                               wrong_ones=sorted(ones-target[1]),
                               missing_ones=sorted(target[1]-ones)))
            if (head, ones) == target[:2]:
                outcome = 'passed_finite_test'
                break
            if len(visits) > 15:
                outcome = 'dispatch_visit_limit'
                break
    result = dict(status=outcome, finite_only=True, case=case, fixture=args.fixture,
                  table_sha256=hashlib.sha256(args.table.read_bytes()).hexdigest(),
                  trace=trace, dispatcher_visits=visits,
                  expected_head=target[0], expected_ones=sorted(target[1]),
                  interpretation='The visit/fuel limit is bounded evidence; it does not prove eventual rejoining impossible.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('trace','dispatcher_visits','expected_ones')}, indent=2))


if __name__ == '__main__':
    main()
