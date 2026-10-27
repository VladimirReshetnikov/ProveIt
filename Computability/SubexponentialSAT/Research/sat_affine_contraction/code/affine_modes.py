#!/usr/bin/env python3
"""Exact affine-plan selection and finite nine-factor contraction.

The mode graph has one Cartesian index per unordered group pair; each is the
product of the original two directed pair domains. The callback for a group
may be expensive and is evaluated once per incident assignment. Matrix-shaped
sums here use ordinary scalar arithmetic, not a fast matrix backend.
"""
from itertools import combinations, product
from math import prod

VERTICES = tuple(range(9))
EDGES = tuple(combinations(VERTICES, 2))
DIRECTIONS = ((1, 0), (0, 1), (1, 1), (1, 2))
PLANS = tuple(tuple(tuple(3*x+y for x in range(3) for y in range(3)
                         if (a*x+b*y) % 3 == c)
                    for c in range(3)) for a, b in DIRECTIONS)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def validate_dimensions(dimensions):
    require(set(dimensions) == set(EDGES), "Exactly the 36 unordered pair domains are required")
    require(all(isinstance(d, int) and not isinstance(d, bool) and d >= 0
                for d in dimensions.values()), "Domain sizes must be nonnegative integers")


def cut(block):
    bb = set(block)
    return tuple(e for e in EDGES if (e[0] in bb) != (e[1] in bb))


def boundary_sets(plan):
    return tuple((x,) for x in VERTICES) + tuple(b[1:] for b in plan) + tuple(plan)


def time_supports(plan):
    ops = []
    for b in plan:
        ops.append(((b[1],), (b[2],), tuple(x for x in VERTICES if x not in b[1:])))
        ops.append(((b[0],), b[1:], tuple(x for x in VERTICES if x not in b)))
    ops.append(plan)
    rows = []
    for op in ops:
        label = {x: j for j, bb in enumerate(op) for x in bb}
        for discounted in combinations(range(3), 2):
            rows.append(tuple(0 if label[x] == label[y]
                              else 2 if tuple(sorted((label[x], label[y]))) == discounted
                              else 5 for x, y in EDGES))
    return tuple(rows)


def select_plan(dimensions):
    """Select by a rounded version of max(F_j, (3/sqrt(7))G_j).

    Ptime=2^(5 F_j), Pspace=2^G_j. For A=ceil(log2(Ptime)) and
    B=ceil(log2(Pspace)), compare max(7*A*A, 225*B*B) exactly.
    This is175 times the square of the rounded objective. Its additive
    error is at most3/sqrt(7), leaving the leading exponent unchanged.
    """
    validate_dimensions(dimensions)
    require(all(dimensions.values()), "Skip an empty Cartesian domain before selecting a plan")
    records = []
    for index, plan in enumerate(PLANS):
        pt = max(prod(dimensions[e]**v for e, v in zip(EDGES, row))
                 for row in time_supports(plan))
        ps = max(prod(dimensions[e] for e in cut(b)) for b in boundary_sets(plan))
        a = (pt-1).bit_length()
        b = (ps-1).bit_length()
        records.append({"plan": index, "Ptime": pt, "Pspace": ps,
                        "A": a, "B": b, "score": max(7*a*a, 225*b*b)})
    best = min(records, key=lambda v: (v["score"], v["plan"]))
    return {"chosen_plan": best["plan"], "Ptime": best["Ptime"],
            "Pspace": best["Pspace"], "score": best["score"], "all_scores": records}


def assignments(axes, dimensions):
    yield from product(*(range(dimensions[e]) for e in axes))


def contract(dimensions, group_value, zero, one, add, multiply, forced_plan=None):
    """Return the finite contraction and paid group-evaluation counts.

    group_value(g, incident_edges, tuple_of_index_values) returns a ring entry.
    Ring operations are supplied; the implementation performs no division.
    """
    validate_dimensions(dimensions)
    if not all(dimensions.values()):
        return zero, {"empty_domain": True, "group_calls": [0]*9,
                      "maximum_table_entries": 0, "chosen_plan": None}
    selection = select_plan(dimensions)
    chosen = selection["chosen_plan"] if forced_plan is None else forced_plan
    require(isinstance(chosen, int) and not isinstance(chosen, bool) and 0 <= chosen < 4,
            "Invalid plan index")
    tables = {}
    calls = [0]*9
    maximum = 0
    for g in VERTICES:
        axes = cut((g,))
        entries = {}
        for state in assignments(axes, dimensions):
            entries[state] = group_value(g, axes, state)
            calls[g] += 1
        tables[frozenset((g,))] = (axes, entries)
        maximum = max(maximum, len(entries))

    def merge(left, right):
        nonlocal maximum
        aa, ab = tables[left], tables[right]
        axes = tuple(e for e in EDGES if e in aa[0] or e in ab[0])
        pos = {e: i for i, e in enumerate(axes)}
        ra = [pos[e] for e in aa[0]]
        rb = [pos[e] for e in ab[0]]
        out_axes = cut(left | right)
        ro = [pos[e] for e in out_axes]
        output = {s: zero for s in assignments(out_axes, dimensions)}
        for state in assignments(axes, dimensions):
            a = aa[1][tuple(state[i] for i in ra)]
            b = ab[1][tuple(state[i] for i in rb)]
            key = tuple(state[i] for i in ro)
            output[key] = add(output[key], multiply(a, b))
        tables[left | right] = (out_axes, output)
        maximum = max(maximum, len(output))
        return left | right

    blocks = []
    for a, b, c in PLANS[chosen]:
        pair = merge(frozenset((b,)), frozenset((c,)))
        blocks.append(merge(frozenset((a,)), pair))
    all_groups = merge(merge(blocks[0], blocks[1]), blocks[2])
    answer = tables[all_groups][1][()]
    expected = [prod(dimensions[e] for e in cut((g,))) for g in VERTICES]
    require(calls == expected, "Incorrect recursive child-call accounting")
    predicted = max(prod(dimensions[e] for e in cut(b))
                    for b in boundary_sets(PLANS[chosen]))
    require(maximum <= predicted, "Unexpected table beyond the boundary bound")
    return answer, {"empty_domain": False, "group_calls": calls,
                    "maximum_table_entries": maximum, "chosen_plan": chosen,
                    "predicted_table_entries": predicted}
