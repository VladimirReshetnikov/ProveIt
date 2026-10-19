#!/usr/bin/env python3
"""Check all guarded instructions with exact full-file affine targets."""
import argparse
import json
from pathlib import Path
from common import LAYOUTS, OUTPUT
from affine_checker import AffineChecker, Tracking, PROTECTED


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('layouts', nargs='*', default=LAYOUTS)
    parser.add_argument('--domain', choices=('unrestricted', 'product'), default='product')
    parser.add_argument('--fuel', type=int, default=1500)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    assert __debug__, 'Assertions required; do not use -O.'
    result = dict(status='PASS', domain=args.domain, protected_rows=len(PROTECTED),
                  symbolic_fuel=args.fuel, formal_kernel_check=False, layouts=[])
    for layout in args.layouts:
        checker = AffineChecker(layout, args.domain)
        used = set()
        maximum = 0
        total = 0
        for index in range(len(checker.cases)):
            table = Tracking(checker.table)
            ok, cost, error = checker.check(table, index, args.fuel)
            assert ok, (layout, index, error)
            used |= table.used
            maximum = max(maximum, cost)
            total += cost
        row = dict(layout=str(layout), guarded_cases=len(checker.cases),
                   literal_rows_used=len(used), maximum_symbolic_rules=maximum,
                   total_symbolic_rules=total, exact_full_box_target=True)
        result['layouts'].append(row)
        print(json.dumps(row), flush=True)
    destination = args.output or OUTPUT / ('affine-' + args.domain + '.json')
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
