#!/usr/bin/env python3
"""Exhaust the fixed twelve-group support certificate with exact integers.

The plan data are a proposed certificate, not executable source. This checker
reconstructs every operation from set membership and every tuple norm from its
Gram expansion. No numerical optimizer or third-party package is required.
"""
from itertools import combinations
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def masks(plan, n=12):
    require(len(plan) == 3 and all(plan), 'Three nonempty blocks required')
    require(sorted(sum(plan, [])) == list(range(n)), 'Not a partition')
    vertices = set(range(n))
    operations = []

    def split(block):
        if len(block) == 1:
            return
        cut = len(block)//2
        left, right = block[:cut], block[cut:]
        split(left)
        split(right)
        operations.append((set(left), set(right), vertices-set(block)))

    for block in plan:
        split(block)
    operations.append(tuple(map(set, plan)))
    rows = []
    for operation in operations:
        for discount in combinations(range(3), 2):
            row = []
            for x, y in combinations(range(n), 2):
                ix = next(i for i, part in enumerate(operation) if x in part)
                iy = next(i for i, part in enumerate(operation) if y in part)
                row.append(0 if ix == iy else 2 if tuple(sorted((ix, iy))) == discount else 5)
            rows.append(tuple(row))
    require(len(rows) == 3*(n-2), 'Wrong operation count')
    return rows


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def exhaust(plans):
    require(len(plans) == 4, 'Four plans required')
    menus = list(map(masks, plans))
    norms = [[dot(v, v) for v in menu] for menu in menus]
    cross = {(i, j): [[dot(a, b) for b in menus[j]] for a in menus[i]]
             for i, j in combinations(range(4), 2)}
    q01,q02,q03,q12,q13,q23 = [cross[p] for p in combinations(range(4), 2)]
    maximum, total, checked, witness = -1, 0, 0, None
    for a in range(30):
        for b in range(30):
            base = norms[0][a] + norms[1][b] + 2*q01[a][b]
            for c in range(30):
                partial = base + norms[2][c] + 2*(q02[a][c]+q12[b][c])
                for d in range(30):
                    value = partial + norms[3][d] + 2*(q03[a][d]+q13[b][d]+q23[c][d])
                    total += value
                    checked += 1
                    if value > maximum:
                        maximum, witness = value, (a,b,c,d)
    # Check the maximizing witness by a different, coordinatewise formula.
    v = [menus[i][j] for i,j in enumerate(witness)]
    direct = sum(sum(row[e] for row in v)**2 for e in range(66))
    require(direct == maximum, 'Gram and coordinatewise maxima disagree')
    return maximum,total,checked,witness,menus


def main():
    data = json.loads((ROOT/'data/twelve_plans.json').read_text())
    maximum,total,checked,witness,menus = exhaust(data['plans'])
    require(maximum == 9864, 'False twelve-group squared-norm certificate')
    require(total == 3494275200, 'Exhaustive checksum mismatch')
    require(checked == 810000, 'Incomplete enumeration')
    require(2*maximum*400 == 137*25*16*12*12, 'Incorrect beta squared')
    # A repeated final plan violates the proposed bound: no averaging gain.
    repeated = max(16*dot(v,v) for v in menus[0])
    require(repeated > maximum, 'Duplicate-plan negative control failed')
    malformed = [list(b) for b in data['plans'][0]]
    malformed[0][0] = malformed[0][1]
    try:
        masks(malformed)
    except ValueError:
        rejected = True
    else:
        rejected = False
    require(rejected, 'Invalid partition accepted')
    print(json.dumps({'status':'PASS','groups':12,'plans':4,'supports_per_plan':30,
      'tuples_checked':checked,'maximum_squared_norm':maximum,
      'squared_norm_sum':total,'first_maximizer':witness,'beta_squared':'137/400',
      'independent_coordinatewise_witness_squared_norm':maximum,
      'negative_controls':{'repeated_plan_exceeds_bound':repeated,'invalid_partition_rejected':rejected}},
      indent=2,sort_keys=True))


if __name__ == '__main__':
    main()
