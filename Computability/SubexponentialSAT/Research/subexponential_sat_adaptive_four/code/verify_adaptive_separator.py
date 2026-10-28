"""Independent finite identities and rational coefficient certificates.

Run: python3 verify_adaptive_separator.py --output adaptive_results.json
Checks use explicit exceptions and remain active under python -O.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from itertools import product
import json
from math import isqrt, log, pi, prod, sqrt
from pathlib import Path
import random

from adaptive_separator import MATCHINGS, build_tree, cardinality_plan, contract, path_edge_sets


def require(test, message):
    if not test:
        raise ArithmeticError(message)


def four_cost(w):
    return sum(w.values()) - max(min(w[e], w[f]) for e, f in MATCHINGS)


def sqrt_bounds(x: F, scale=10**9):
    x = F(x)
    lower_integer = isqrt(x.numerator * scale * scale // x.denominator)
    lo = F(lower_integer, scale)
    hi = lo if lo * lo == x else F(lower_integer + 1, scale)
    require(lo * lo <= x <= hi * hi, "square-root enclosure")
    return lo, hi


def certificate(g16, g8, g4, upper):
    # pi<22/7, ln2>693/1000; and pi>314/100, ln2<694/1000.
    # These coarse classical rational bounds already separate the certificates.
    side = 1 if upper else 0
    p = F(22, 7) if upper else F(314, 100)
    ln2 = F(693, 1000) if upper else F(694, 1000)
    root = F(9, 128) * sqrt_bounds(F(80) * g16)[side]
    second = sqrt_bounds(F(120) * g8)[side] / 512
    tail = (sqrt_bounds(F(160) * g4)[side] / 1024
            / (1 - sqrt_bounds(F(2, 5))[side]))
    return p * sqrt_bounds(F(2))[side] / ln2 * (root + second + tail)


def numerical_coefficient(g16, g8, g4):
    return pi * sqrt(2) / log(2) * (
        9 / 128 * sqrt(80 * g16)
        + sqrt(120 * g8) / 512
        + sqrt(160 * g4) / 1024 / (1 - sqrt(2 / 5)))


def direct(groups, domains, factor, zero, one, add, mul):
    """Independent literal sum over all edge assignments."""
    edges = tuple(domains)
    answer = zero
    for vals in product(*(domains[e] for e in edges)):
        assignment = dict(zip(edges, vals))
        term = one
        for g in groups:
            local = {e: assignment[e] for e in edges if g in e}
            term = mul(term, factor(g, local))
        answer = add(answer, term)
    return answer


def main():
    rng = random.Random(20261026)
    undirected = tuple((i, j) for i in range(4) for j in range(i + 1, 4))
    exhaustive = 0
    for vals in product(range(6), repeat=6):
        w = dict(zip(undirected, vals))
        c = four_cost(w)
        require(3 * c * c <= 13 * sum(x * x for x in vals), "four-group sharp inequality")
        exhaustive += 1
    # In each opposite-edge pair take one 2 and one 3.  The equality is exact.
    extremal = {}
    for a, b in MATCHINGS:
        extremal[a] = 2
        extremal[b] = 3
    require(3 * four_cost(extremal)**2 == 13 * sum(x*x for x in extremal.values()),
            "sharpness of undirected four-group constant")
    directed_extremal = {(i, j): extremal[min(i, j), max(i, j)]
                          for i in range(4) for j in range(4) if i != j}
    et = build_tree(range(4), {e: 2**w for e, w in directed_extremal.items()})
    ep = path_edge_sets(et, tuple(directed_extremal))
    ec = max(sum(directed_extremal[e] for e in path) for path in ep.values())
    en = sum(w*w for w in directed_extremal.values())
    require(F(ec*ec, en) == F(26, 3), "sharp directed fixture")

    expected = {4:F(26,3), 6:F(202,9), 8:F(110,3), 12:F(84),
                13:F(314,3), 14:F(118), 16:F(442,3)}
    for r, value in expected.items():
        require(cardinality_plan(r)[0] == value, "cardinality dynamic program")
    tree_inequalities = 0
    for r in (4, 5, 6, 7, 8, 12, 13, 14, 16, 20, 32, 64):
        edges = tuple((i, j) for i in range(r) for j in range(r) if i != j)
        for _ in range(60):
            h = {e: rng.randrange(8) for e in edges}
            tree = build_tree(range(r), {e: 1 << h[e] for e in edges})
            paths = path_edge_sets(tree, edges)
            cost = max(sum(h[e] for e in path) for path in paths.values())
            require(cost*cost <= cardinality_plan(r)[0] * sum(x*x for x in h.values()),
                    "hierarchical path bound")
            tree_inequalities += 1

    contractions = 0
    total_calls = 0
    for modulus in (8, 27, 64):
        for r in (2, 3, 4, 5, 8, 16):
            edges = [(i,j) for i in range(r) for j in range(r) if i != j]
            for case in range(12):
                active = rng.sample(edges, min(len(edges), rng.randrange(1,8)))
                domains = {e: range(rng.randrange(1,4)) for e in active}
                # Ring Z/modulus[epsilon]/epsilon^2: not a field.
                def add(x,y): return ((x[0]+y[0])%modulus,(x[1]+y[1])%modulus)
                def mul(x,y): return ((x[0]*y[0])%modulus,(x[0]*y[1]+x[1]*y[0])%modulus)
                def factor(g, assignment):
                    first = 2*g + 1 + sum((3*a+5*b+7)*v for (a,b),v in assignment.items())
                    second = g*g + sum((a+b+1)*(v*v+1) for (a,b),v in assignment.items())
                    return first%modulus, second%modulus
                answer, stats = contract(range(r),domains,factor,zero=(0,0),one=(1,0),
                                         add=add,multiply=mul)
                oracle = direct(range(r),domains,factor,(0,0),(1,0),add,mul)
                require(answer == oracle, "exact ring contraction")
                require(stats["factor_calls"] == stats["predicted_factor_calls"], "paid child calls")
                total_calls += stats["total_factor_calls"]
                contractions += 1
    empty, stats = contract(range(4), {(0,1): ()}, lambda g,x: 1)
    require(empty == 0 and stats["total_factor_calls"] == 0, "empty domain handling")

    upper = certificate(F(442,3),F(110,3),F(26,3),True)
    prior_lower = certificate(F(170),F(42),F(10),False)
    require(upper < 51, "eventual coefficient 51")
    require(prior_lower > 54, "matched prior coefficient exceeds 54")
    require(upper < prior_lower, "strict matched improvement")

    # Exact leading packing capacities for the final simple schedule.
    require(F(1,80)*8 + F(9,10) == 1, "symmetric root gate")
    require(F(1,40)*4 + F(9,10) == 1, "depth-one asymmetric gate")
    require(F(1,30)*3 + F(9,10) == 1, "depth-two asymmetric gate")
    require(F(1,20)*2 + F(9,10) == 1, "tail asymmetric gate")
    require(F(1,80)+F(1,80)+F(1,120)+F(1,160)/(1-F(5,8)) == F(1,20),
            "total cumulative capacity")
    # Uniform floor/depth lower bound: eventual child ratio 3/5, taper5/8.
    require(F(3,5)<F(5,8), "positive taper depth exponent")

    report = {
        "status":"passed", "seed":20261026,
        "exhaustive_four_group_weight_vectors":exhaustive,
        "hierarchical_path_inequalities":tree_inequalities,
        "exact_nilpotent_ring_contractions":contractions,
        "total_explicitly_counted_factor_calls":total_calls,
        "four_group_equality_ratio":str(F(ec*ec,en)),
        "cardinality_certificates":{str(r):{"squared_norm":str(cardinality_plan(r)[0]),
                                         "split":cardinality_plan(r)[1]} for r in range(1,33)},
        "new_coefficient_numeric_diagnostic":numerical_coefficient(442/3,110/3,26/3),
        "matched_prior_coefficient_numeric_diagnostic":numerical_coefficient(170,42,10),
        "new_coefficient_rational_upper":str(upper),
        "new_coefficient_rational_upper_decimal":float(upper),
        "matched_prior_coefficient_rational_lower":str(prior_lower),
        "matched_prior_coefficient_rational_lower_decimal":float(prior_lower),
        "safe_eventual_coefficient":51,
        "scope":"Finite graph identities and a relative normalized-wire certificate; no global SAT order improvement."
    }
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    text=json.dumps(report,indent=2,sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(text)
    print(text)


if __name__ == "__main__":
    main()
