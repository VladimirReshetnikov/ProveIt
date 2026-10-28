#!/usr/bin/env python3
"""Exact anchored-rectangle certificate for twelve affine ten-group plans.

Standalone standard-library checker. It constructs its own affine plans,
support vectors, pair potentials, and compatibility search. It verifies a
finite analytic certificate, not an implementation of fast multiplication
or an end-to-end SAT solver.
"""
from fractions import Fraction as Q
from itertools import combinations, permutations
from math import isqrt, lcm
from pathlib import Path
import json
import time

ALPHA = Q(321333, 1000000)
OMEGA = Q(2371553, 1000000)
EPSILON = Q(1, 1000000)
D = 1 + EPSILON / 2
SOURCE_ANCHORS = ((Q(11, 20), Q(2066134, 1000000)),
                  (Q(3, 5), Q(2092631, 1000000)))
PADDED_ANCHORS = tuple((k, cost+EPSILON) for k, cost in SOURCE_ANCHORS)
ANCHOR_K = Q(59261, 103891)
ANCHOR_COST = Q(26972100941, 12986375000)
C = (OMEGA-1)/2
W = (ANCHOR_COST-2-EPSILON)/(ANCHOR_K-ALPHA)
V = 1+EPSILON-ALPHA*W
BETA13_SQUARED = Q(57151369949899, 169000000000000)
SCALE = lcm(D.denominator, V.denominator, W.denominator, C.denominator)
TRIPLES = sorted(set(permutations((int(D*SCALE), int(D*SCALE), 0))) |
                 set(permutations((SCALE, int(V*SCALE), int(W*SCALE)))) |
                 set(permutations((SCALE, int(C*SCALE), int(C*SCALE)))))
EDGES = tuple(combinations(range(10), 2))


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def plans():
    result = []
    forms = ((1, 0), (0, 1), (1, 1), (1, 2))
    for a, b in forms:
        lines = [[3*x+y for x in range(3) for y in range(3)
                  if (a*x+b*y) % 3 == c] for c in range(3)]
        for k in range(3):
            result.append([lines[k]+[9]] +
                          [lines[j][:] for j in range(3) if j != k])
    return result


def supports(plan):
    require(sorted(sum(plan, [])) == list(range(10)), 'partition')
    operations = []

    def merge(block):
        if len(block) == 1:
            return
        mid = len(block)//2
        left, right = block[:mid], block[mid:]
        merge(left)
        merge(right)
        operations.append((set(left), set(right),
                           set(range(10))-set(block)))

    for block in plan:
        merge(block)
    operations.append(tuple(map(set, plan)))
    rows = []
    for parts in operations:
        part_of = {v: i for i, part in enumerate(parts) for v in part}
        for triple in TRIPLES:
            weights = dict(zip(((0, 1), (0, 2), (1, 2)), triple))
            rows.append(tuple(0 if part_of[a] == part_of[b] else
                              weights[tuple(sorted((part_of[a], part_of[b])))]
                              for a, b in EDGES))
    require(len(rows) == 96, 'support count')
    return rows


def exact_certificate():
    menu_plans = plans()
    menus = [supports(p) for p in menu_plans]
    q = len(menus)
    require(q == 12, 'plan count')
    norms = [[dot(v, v) for v in menu] for menu in menus]
    pair = {}
    for i, j in combinations(range(q), 2):
        pair[i, j] = [[norms[i][a] + norms[j][b] +
                       2*(q-1)*dot(v, w)
                       for b, w in enumerate(menus[j])]
                      for a, v in enumerate(menus[i])]

    def tuple_norm(choice):
        v = [sum(menus[i][a][e] for i, a in enumerate(choice))
             for e in range(len(EDGES))]
        return dot(v, v)

    witness = [88]*q
    candidate = tuple_norm(witness)
    target = (q-1)*candidate
    require(sum(pair[i, j][witness[i]][witness[j]]
                for i, j in pair) == target, 'pair identity at witness')
    domains = [list(range(96)) for _ in range(q)]
    rounds = []
    excluded_bounds = []
    old_pair = sum(max(map(max, table)) for table in pair.values())
    while True:
        maxima = {(i, j): max(pair[i, j][a][b]
                             for a in domains[i] for b in domains[j])
                  for i, j in pair}
        new_domains = []
        exclusions = []
        for i in range(q):
            base = sum(value for (j, k), value in maxima.items()
                       if i not in (j, k))
            kept = []
            for a in domains[i]:
                upper = base
                for j in range(q):
                    if j < i:
                        upper += max(pair[j, i][b][a] for b in domains[j])
                    elif j > i:
                        upper += max(pair[i, j][a][b] for b in domains[j])
                if upper >= target:
                    kept.append(a)
                else:
                    exclusions.append(upper)
            require(witness[i] in kept, 'witness was excluded')
            new_domains.append(kept)
        rounds.append([len(x) for x in new_domains])
        excluded_bounds.extend(exclusions)
        if new_domains == domains:
            break
        domains = new_domains

    reduced = {(i, j): [[pair[i, j][a][b] for b in domains[j]]
                        for a in domains[i]] for i, j in pair}
    future = [sum(max(map(max, table)) for (i, j), table in reduced.items()
                  if i >= depth) for depth in range(q+1)]
    visited = [0]*(q+1)
    pruned = [0]*(q+1)
    leaf_count = 0
    max_leaf = 0

    def visit(depth, value, unary):
        nonlocal leaf_count, max_leaf
        visited[depth] += 1
        if depth == q:
            leaf_count += 1
            max_leaf = max(max_leaf, value)
            require(value <= target, 'candidate norm is not maximal')
            return
        upper = value + sum(max(v) for v in unary[depth:]) + future[depth]
        if upper <= target:
            pruned[depth] += 1
            return
        for a in range(len(domains[depth])):
            following = unary[:]
            for j in range(depth+1, q):
                following[j] = [x+y for x, y in
                                zip(unary[j], reduced[depth, j][a])]
            visit(depth+1, value+unary[depth][a], following)

    visit(0, 0, [[0]*len(d) for d in domains])
    require(all(x < target for x in excluded_bounds), 'elimination threshold')
    beta2 = Q(2*candidate, SCALE*SCALE*q*q*100)
    pair_beta2 = Q(2*old_pair, (q-1)*SCALE*SCALE*q*q*100)
    require(beta2 < pair_beta2, 'consistency improvement')
    return dict(status='PASS', alpha=str(ALPHA), omega=str(OMEGA),
                epsilon=str(EPSILON), coefficients=list(map(str, (D, V, W))),
                symmetric_coefficient=str(C),
                source_anchors=[[str(k), str(cost)] for k, cost in SOURCE_ANCHORS],
                padded_anchors=[[str(k), str(cost)] for k, cost in PADDED_ANCHORS],
                interpolated_anchor=[str(ANCHOR_K), str(ANCHOR_COST)],
                scale=SCALE, triples=[list(t) for t in TRIPLES],
                plans=menu_plans, support_count=q*96,
                pair_choices=len(pair)*96**2,
                witness=witness, maximum_squared_norm=candidate,
                threshold=target, surviving_indices=domains,
                pruning_rounds=rounds,
                maximum_excluded_bound=max(excluded_bounds),
                search_nodes_by_depth=visited,
                pruned_nodes_by_depth=pruned,
                visited_leaves=leaf_count, maximum_visited_leaf=max_leaf,
                beta_squared=str(beta2), independent_pair_beta_squared=str(pair_beta2))


def atan_interval(d, terms):
    s = sum((Q((-1)**j, (2*j+1)*d**(2*j+1))
             for j in range(terms)), Q(0))
    t = s + Q((-1)**terms, (2*terms+1)*d**(2*terms+1))
    return min(s, t), max(s, t)


def schedule(beta2):
    a, b = atan_interval(5, 30)
    c, d = atan_interval(239, 10)
    pi_lo, pi_hi = 16*a-4*d, 16*b-4*c
    count = 60
    ln_lo = sum((Q(2, (2*j+1)*3**(2*j+1))
                 for j in range(count)), Q(0))
    ln_hi = ln_lo + Q(2, (2*count+1)*3**(2*count+1))*Q(9, 8)

    def sqrt_interval(x):
        den = 10**30
        r = isqrt(x.numerator*den*den//x.denominator)
        require(Q(r*r, den*den) <= x < Q((r+1)**2, den*den), 'square root')
        return Q(r, den), Q(r+1, den)

    def coeff(radicals):
        roots = [sqrt_interval(x) for x in radicals]
        return (pi_lo/ln_hi*sum((v[0] for v in roots), Q(0)),
                pi_hi/ln_lo*sum((v[1] for v in roots), Q(0)))

    values = {
        'root': coeff([2*beta2/Q(301, 20000)]),
        'depth_one': coeff([Q(7200, 301), Q(800, 119)*BETA13_SQUARED]),
        'depth_one_old_backend': coeff([Q(7200, 301), Q(50304, 20111)]),
        'infinite_tail': coeff([Q(7200, 301), Q(19200, 20111), Q(77760, 261781)]),
        'old_nine_consistency': coeff([2*Q(39711821767968409,
                                          122500000000000000)/Q(301, 20000)])}
    require(values['root'][0] > values['depth_one'][1], 'root vs depth one')
    require(values['root'][0] > values['infinite_tail'][1], 'root vs tail')
    require(values['root'][1] < values['old_nine_consistency'][0], 'strict gain')
    require(values['depth_one'][1] < values['old_nine_consistency'][0], 'complete strict gain')
    require(values['root'][1] < Q(29149, 1000), 'eventual coefficient 29.149')
    return dict(beta13_squared=str(BETA13_SQUARED),
                beta13_certificate='check_anchored_thirteen.py',
                eventual_coefficient='29.149',
                intervals={k: list(map(str, v)) for k, v in values.items()},
                displays={k: float(v[0]) for k, v in values.items()})


if __name__ == '__main__':
    start = time.perf_counter()
    require(0 < W < V < 1 < D, 'coefficient ordering')
    require(ALPHA < Q(321334, 1000000), 'strict dual-exponent slack')
    require(OMEGA > Q(2371552, 1000000), 'strict square-exponent slack')
    require(1+2*C == OMEGA, 'square endpoint')
    require(ANCHOR_COST == 1+C*(1+ANCHOR_K), 'anchor identity')
    (ka, ba), (kb, bb) = PADDED_ANCHORS
    require(ka < ANCHOR_K < kb, 'anchor location')
    require(ANCHOR_COST == ((kb-ANCHOR_K)*ba+(ANCHOR_K-ka)*bb)/(kb-ka),
            'anchor interpolation')
    (ka0, ba0), (kb0, bb0) = SOURCE_ANCHORS
    require(ANCHOR_COST-((kb0-ANCHOR_K)*ba0+(ANCHOR_K-ka0)*bb0)/(kb0-ka0)
            == EPSILON, 'strict interpolated-anchor slack')
    require(0 < W < C < V < 1 < D, 'piecewise slopes and symmetry')
    require(SCALE == 51754786594000000, 'integral coefficient scale')
    result = exact_certificate()
    result['schedule'] = schedule(Q(result['beta_squared']))
    result['elapsed_seconds'] = time.perf_counter()-start
    output = Path(__file__).with_name('anchored_backend_certificate.json')
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('plans', 'triples', 'surviving_indices', 'schedule')}, indent=2))
    print(json.dumps(result['schedule']['displays'], indent=2))
