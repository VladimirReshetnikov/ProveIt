#!/usr/bin/env python3
"""Exact contraction-plan menus and integer selectors.

This is component software, not a SAT solver or fast matrix backend.
The standalone JSON data freeze the finite certificates used in the report.
"""
from itertools import combinations
from math import prod
from pathlib import Path
import argparse
import json

DATA = Path(__file__).resolve().parents[1] / 'data' / 'portfolios.json'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_menus():
    return json.loads(DATA.read_text(encoding='utf-8'))['menus']


def affine_plans():
    return [[[3*x+y for x in range(3) for y in range(3)
              if ((y-direction*x) % 3 if direction < 3 else x) == c]
             for c in range(3)] for direction in range(4)]


def puncture(plans, deleted):
    return [[[v for v in block if v not in deleted] for block in plan]
            for plan in plans]


def operations(r, plan):
    require(len(plan) == 3 and all(plan), 'Three nonempty blocks required')
    require(sorted(v for block in plan for v in block) == list(range(r)),
            'Blocks must partition exactly the group labels')
    answer = []
    universe = set(range(r))

    def build(block):
        if len(block) == 1:
            return
        middle = len(block)//2
        left, right = block[:middle], block[middle:]
        build(left)
        build(right)
        outside = sorted(universe.difference(block))
        answer.append((tuple(left), tuple(right), tuple(outside)))

    for block in plan:
        build(block)
    answer.append(tuple(tuple(block) for block in plan))
    require(len(answer) == r-2, 'Operation-count identity failed')
    return answer


def supports(r, plan):
    edges = list(combinations(range(r), 2))
    result = []
    for op in operations(r, plan):
        labels = {v: j for j, part in enumerate(op) for v in part}
        for discount in combinations(range(3), 2):
            row = []
            for x, y in edges:
                pair = tuple(sorted((labels[x], labels[y])))
                row.append(0 if pair[0] == pair[1]
                           else 2 if pair == discount else 5)
            result.append(tuple(row))
    return result


def select_plan(r, directed_dimensions, plans=None):
    if plans is None:
        matches = [m for m in load_menus() if m['groups'] == r]
        require(len(matches) == 1, 'No unique frozen menu for this group count')
        plans = matches[0]['plans']
    require(set(directed_dimensions) == {(i,j) for i in range(r)
                                         for j in range(r) if i != j},
            'Exactly all directed pairs are required')
    require(all(isinstance(n,int) and not isinstance(n,bool) and n > 0
                for n in directed_dimensions.values()),
            'Skip empty allocations first; dimensions must be positive integers')
    dims = [directed_dimensions[i,j]*directed_dimensions[j,i]
            for i,j in combinations(range(r),2)]
    scores = [max(prod(n**v for n,v in zip(dims,row))
                  for row in supports(r,plan)) for plan in plans]
    j = min(range(len(plans)), key=lambda k: (scores[k],k))
    return {'groups':r, 'selected_plan':j, 'plan':plans[j],
            'cost_powers_five':scores, 'selected_cost_power_five':scores[j]}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dimensions',type=Path,required=True,
                        help='JSON with groups and dimensions [[g,h,cardinality],...]')
    args=parser.parse_args()
    x=json.loads(args.dimensions.read_text(encoding='utf-8'))
    result=select_plan(x['groups'],{(g,h):n for g,h,n in x['dimensions']})
    print(json.dumps(result,indent=2,sort_keys=True))
