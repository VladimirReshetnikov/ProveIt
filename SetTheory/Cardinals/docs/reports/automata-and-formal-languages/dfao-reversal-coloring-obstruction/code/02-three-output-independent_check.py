#!/usr/bin/env python3
"""Independent arithmetic and finite-graph cross-checks; imports no project code."""
from __future__ import annotations
import json
from math import gcd
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def cycle_count(length: int) -> int:
    # Fix the first color. 'same'/'other' count paths ending in that color
    # or one of the other two colors. Closing the cycle requires 'other'.
    same, other = 1, 0
    for _ in range(1, length):
        same, other = other, 2 * same + other
    return 3 * other


def main() -> None:
    # A max-product composition recurrence, independent of the mod-3 formula.
    j = [1]
    for r in range(1, 13):
        j.append(max(part * j[r-part] for part in range(1, r+1)))
    rows = []
    cycle_min = []
    for m in range(2, 13):
        counts = [cycle_count(m // gcd(m, h)) ** gcd(m, h)
                  for h in range(1, m)]
        cycle_min.append({'m': m, 'minimum_proper': min(counts),
                          'minimizing_displacements': [h for h in range(1,m)
                                                      if counts[h-1] == min(counts)]})
    for n in range(7, 13):
        values = [(cycle_count(m // gcd(m,h)) ** gcd(m,h) * 3**(n-m)
                   - m*j[n-m], m, h)
                  for m in range(2,n+1) for h in range(1,m)]
        value,m,h = min(values)
        rows.append({'n':n, 'minimum':value, 'm':m, 'displacement':h})
    recorded = json.loads((ROOT/'data'/'verification.json').read_text())
    check([r['minimum'] for r in rows] ==
          [r['minimum'] for r in recorded['same_cycle_table']], 'Small table mismatch')
    checks = 0
    for n in range(7, 1001):
        h = n//2
        if n % 2:
            d = 9*2**h-h-7
        elif n % 4 == 0:
            d = 15*2**(h-1)-h-7
        else:
            d = 51*2**(h-2)-h-8
        options = [3*(2**a+2**(n-a)-2)-(n-a)
                   for a in range(1,(n+1)//2) if gcd(a,n-a)==1]
        check(d == min(options), f'Closed form failure at {n}')
        checks += 1
    def d(n: int) -> int:
        h=n//2
        return (9*2**h-h-7 if n%2 else
                15*2**(h-1)-h-7 if n%4==0 else 51*2**(h-2)-h-8)
    for n in range(7,989):
        check(d(n+12)-6*d(n+8)+9*d(n+4)-4*d(n)==0,'Recurrence failure')
    result={'status':'PASS','independence':'No imports from verify.py; transfer recurrence '
            'for cycles, max-product composition recurrence for residuals, and literal '
            'coprime-split enumeration.', 'cycle_minima':cycle_min,'same_cycle_table':rows,
            'closed_form_checks':checks,'closed_form_range':[7,1000],
            'recurrence_checks':982, 'product_bounds_0_to_12':j}
    (ROOT/'data'/'independent_check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
