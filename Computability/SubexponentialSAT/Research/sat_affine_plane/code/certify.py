#!/usr/bin/env python3
"""Exact support certificates and a paid cached-contraction schedule.

Python standard library only. Run: python3 certify.py
The checks remain active under python -O. This verifies the finite certificate
and schedule arithmetic; it is not an end-to-end SAT solver or proof assistant.
"""
from fractions import Fraction as F
from itertools import combinations
from math import isqrt, prod
from pathlib import Path
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def operation_parts(r, blocks):
    require(len(blocks) == 3 and all(blocks), 'Need three nonempty final blocks')
    require(sorted(sum(blocks, [])) == list(range(r)), 'Blocks must partition all vertices')
    result = []
    universe = set(range(r))

    def construct(block):
        if len(block) < 2:
            return
        cut = len(block) // 2
        left, right = block[:cut], block[cut:]
        construct(left)
        construct(right)
        result.append((left, right, sorted(universe - set(block))))

    for block in blocks:
        construct(block)
    result.append(blocks)
    require(len(result) == r - 2, 'Operation count')
    return result


def masks(r, blocks):
    edge_order = list(combinations(range(r), 2))
    result = []
    for parts in operation_parts(r, blocks):
        owner = {v: i for i, part in enumerate(parts) for v in part}
        for discounted in combinations(range(3), 2):
            v = []
            for x, y in edge_order:
                pair = tuple(sorted((owner[x], owner[y])))
                v.append(0 if pair[0] == pair[1] else 2 if pair == discounted else 5)
            result.append(tuple(v))
    return result


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def certify_four(r, plans):
    """Enumerate all support tuples using exact precomputed Gram entries."""
    require(len(plans) == 4, 'This checker expects exactly four plans')
    menus = [masks(r, p) for p in plans]
    norm = [[dot(v, v) for v in menu] for menu in menus]
    gram = {(a, b): [[dot(v, w) for w in menus[b]] for v in menus[a]]
            for a, b in combinations(range(4), 2)}
    g01, g02, g03 = gram[0, 1], gram[0, 2], gram[0, 3]
    g12, g13, g23 = gram[1, 2], gram[1, 3], gram[2, 3]
    maximum = -1
    witness = None
    checksum = 0
    count = 0
    maximum_count = 0
    for i in range(len(menus[0])):
        for j in range(len(menus[1])):
            base2 = norm[0][i] + norm[1][j] + 2*g01[i][j]
            for k in range(len(menus[2])):
                base3 = base2 + norm[2][k] + 2*(g02[i][k] + g12[j][k])
                for ell in range(len(menus[3])):
                    value = base3 + norm[3][ell] + 2*(g03[i][ell] + g13[j][ell] + g23[k][ell])
                    count += 1
                    checksum += value
                    if value > maximum:
                        maximum, witness, maximum_count = value, [i, j, k, ell], 1
                    elif value == maximum:
                        maximum_count += 1
    # Independently recompute the maximizing vector, not just its Gram formula.
    total = [sum(menus[t][witness[t]][e] for t in range(4))
             for e in range(r*(r-1)//2)]
    require(dot(total, total) == maximum, 'Direct witness agrees with Gram calculation')
    require(count == prod(map(len, menus)), 'All support tuples were enumerated')
    return {'groups': r, 'plan_count': 4, 'masks_per_plan': list(map(len, menus)),
            'Q': maximum, 'b_squared': str(F(2*maximum, 25*16*r*r)),
            'tuples_checked': count, 'first_maximum_tuple': witness,
            'maximum_multiplicity': maximum_count, 'squared_norm_sum': checksum,
            'single_norm_maxima': list(map(max, norm)),
            'pair_dot_maxima': {str(k): max(map(max, v)) for k, v in gram.items()}}


def select_plan(r, plans, directed_sizes):
    """Exact selector. directed_sizes[(a,b)] is a positive list cardinality."""
    products = []
    for a, b in combinations(range(r), 2):
        x, y = directed_sizes[a, b], directed_sizes[b, a]
        require(type(x) is int and type(y) is int and min(x, y) > 0,
                'Directed dimensions must be positive integers')
        products.append(x*y)
    scores = [max(prod(size**v for size, v in zip(products, mask))
                  for mask in masks(r, plan)) for plan in plans]
    chosen = min(range(len(plans)), key=lambda j: (scores[j], j))
    return {'chosen': chosen, 'cost_power_five': scores[chosen],
            'all_costs_power_five': scores, 'plan': plans[chosen]}


def atan_bounds(x, n):
    total = sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n)), F(0))
    next_term = (-1)**n*x**(2*n+1)/F(2*n+1)
    return min(total, total+next_term), max(total, total+next_term)


def constants():
    a, b = atan_bounds(F(1, 5), 50)
    c, d = atan_bounds(F(1, 239), 15)
    pi_bounds = (16*a-4*d, 16*b-4*c)
    n, x = 50, F(1, 3)
    lower = 2*sum((x**(2*j+1)/F(2*j+1) for j in range(n)), F(0))
    upper = lower + 2*x**(2*n+1)/(F(2*n+1)*(1-x*x))
    return pi_bounds, (lower, upper)


def sqrt_bounds(x, digits=50):
    scale = 10**digits
    floor = isqrt(x.numerator*scale*scale//x.denominator)
    low, high = F(floor, scale), F(floor+1, scale)
    require(low*low <= x <= high*high, 'Square-root enclosure')
    return low, high


def coefficient_bounds(radicals):
    (pl, pu), (ll, lu) = constants()
    terms = list(map(sqrt_bounds, radicals))
    return pl*sum(t[0] for t in terms)/lu, pu*sum(t[1] for t in terms)/ll


def decimal_bound(x, upward):
    with localcontext() as ctx:
        ctx.prec = 60
        ctx.rounding = ROUND_CEILING if upward else ROUND_FLOOR
        return str(Decimal(x.numerator)/Decimal(x.denominator))


def render(bounds):
    return [decimal_bound(bounds[0], False), decimal_bound(bounds[1], True)]


def schedule_certificate():
    v0, v1, v2, rho = F(15773, 1000000), F(9, 800), F(8597, 1800000), F(4, 9)
    a9, a13, a7 = F(16, 81), F(24, 169), F(12, 49)
    b9, b13, b7 = F(1, 3), F(601, 1690), F(632, 1225)
    tail_masks = masks(7, [[0, 1, 2], [3, 4], [5, 6]])
    require(max(dot(v, v) for v in tail_masks) == 316, 'Seven-group fixed tail support bound')
    require(a9 < b9 and a13 < b13 and a7 < b7, 'Singleton caches fit the local operation bounds')
    total = v0+v1+v2/(1-rho)
    require(total == F(1781, 50000), 'Exact total capacity')
    require(v0+v1 == F(27023, 1000000), 'Exact first-stage capacity')
    for base, exponent in [(9, 316993), (13, 370044), (7, 280736)]:
        require(base**100000 < 2**exponent, 'Exact logarithm upper bound for '+str(base))
    log9, log13, log7 = F(316993, 100000), F(370044, 100000), F(280736, 100000)
    gaps = [1-F(9, 10)-2*v0*log9,
            1-F(9, 10)-(v0+v1)*log13,
            1-F(9, 10)-total*log7]
    require(min(gaps) > 0, 'Strict degree-packing margins')
    require(total*(2*log13+1) < 1, 'Fresh-side and packet-capacity margins')
    require(total < F(9, 10), 'Fresh packet degrees below original degree cap')
    require(F(9, 4)**3 < 3**4, 'Positive active-depth exponent for every retained taper')
    gamma = F(3, 7)
    tail_squared = a7/(1-gamma)**2
    require(tail_squared == F(3, 4) and tail_squared > b7,
            'Infinite cache tail dominates all tail aggregation terms')
    arguments = {
        'root': [2*b9/v0],
        'depth_one': [2*a9/v0, 2*F(2, 9)**2*b13/v1],
        'infinite_tail': [2*a9/v0, 2*F(2, 9)**2*a13/v1,
                          2*F(4, 117)**2*tail_squared/v2]}
    intervals = {name: coefficient_bounds(values) for name, values in arguments.items()}
    require(intervals['depth_one'][0] > max(intervals['root'][1], intervals['infinite_tail'][1]),
            'Depth-one branch is the proved time maximum')
    require(intervals['depth_one'][1] < F(30692, 1000), 'Eventual time coefficient below 30.692')
    require(intervals['root'][1] < F(29467, 1000), 'Eventual space coefficient below 29.467')
    space1 = coefficient_bounds([2*F(2, 9)**2*b13/v1])
    space2 = coefficient_bounds([2*F(4, 117)**2*b7/v2])
    require(intervals['root'][0] > max(space1[1], space2[1]), 'Root dominates all local storage')
    require(intervals['depth_one'][1] < F(30891, 1000), 'Strict improvement over old time certificate')
    require(intervals['root'][1] < F(30753, 1000), 'Strict improvement over old space certificate')
    return {'alphabets': [9, 13, 7], 'eta_prefix_and_tail_start': list(map(str, [v0, v1, v2])),
            'tail_ratio': str(rho), 'total_capacity': str(total), 'packing_gaps': list(map(str, gaps)),
            'coefficient_intervals': {k: render(v) for k, v in intervals.items()},
            'radical_arguments': {k: list(map(str, v)) for k, v in arguments.items()},
            'later_space_intervals': {'depth_one': render(space1), 'tail': render(space2)},
            'eventual_time_upper': '30.692', 'eventual_space_upper': '29.467'}


def main():
    data = json.loads(Path(__file__).with_name('portfolios.json').read_text())
    results = []
    for entry in data['portfolios']:
        result = certify_four(entry['groups'], entry['plans'])
        require(result['Q'] == entry['expected_Q'], 'Portfolio maximum matches exact data')
        require(result['b_squared'] == entry['expected_b_squared'], 'Normalized coefficient matches data')
        results.append(result)
    print(json.dumps({'status': 'PASS', 'arithmetic': 'Exact integers and fractions',
                      'portfolios': results, 'schedule': schedule_certificate()}, indent=2))


if __name__ == '__main__':
    main()
