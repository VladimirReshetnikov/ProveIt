#!/usr/bin/env python3
"""Small exact regrouping/selector checks over (Z/64Z)[e]/(e^2).

This uses ordinary scalar arithmetic, not the asymptotic matrix backend.
Fixtures use power-of-two domains so the joint selector compares exact
integer logarithms without constructing huge integer cardinality products.
"""
from itertools import combinations, product
from math import prod
from pathlib import Path
import json
import random
from certify import plan_data, dot, require

ROOT = Path(__file__).resolve().parents[1]
MODULUS = 64
ZERO, ONE = (0, 0), (1, 0)


def add(x, y):
    return ((x[0]+y[0]) % MODULUS, (x[1]+y[1]) % MODULUS)


def multiply(x, y):
    return (x[0]*y[0] % MODULUS,
            (x[0]*y[1]+x[1]*y[0]) % MODULUS)


def assignments(edge_ids, dimensions):
    return product(*(range(dimensions[e]) for e in edge_ids))


def joint_selector(plans, dimensions):
    require(all(type(d) is int and d > 0 and d & (d-1) == 0 for d in dimensions),
            'selector fixtures require positive power-of-two domains')
    exponents = [d.bit_length()-1 for d in dimensions]
    scores = []
    for plan in plans:
        rows, boundaries, _ = plan_data(10, plan)
        scores.append(max(max(dot(v,exponents) for v in rows),
                          1470000*max(dot(v,exponents) for v in boundaries)))
    return min(range(len(plans)), key=lambda i: (scores[i],i)), scores


def fixture(dimensions, random_source, zero_factor=False):
    edges = list(combinations(range(10), 2))
    incidence = [[e for e, pair in enumerate(edges) if v in pair] for v in range(10)]
    factors = []
    for v in range(10):
        factors.append({key: ZERO if zero_factor and v == 0 else
                        (random_source.randrange(64),random_source.randrange(64))
                        for key in assignments(incidence[v],dimensions)})
    return edges, incidence, factors


def direct(dimensions, incidence, factors):
    result = ZERO
    for assignment in assignments(range(len(dimensions)),dimensions):
        value = ONE
        for v in range(10):
            value = multiply(value, factors[v][tuple(assignment[e] for e in incidence[v])])
        result = add(result,value)
    return result


def evaluate_plan(plan, dimensions, edges, incidence, factors):
    require(len(dimensions) == len(edges) and all(type(d) is int and d >= 0 for d in dimensions),
            'invalid index domains')
    if any(d == 0 for d in dimensions):
        return ZERO, 0
    plan_data(10, plan)  # Validate the partition before constructing any table.
    paid_calls = 0

    def leaf(v):
        nonlocal paid_calls
        table = {}
        for key in assignments(incidence[v],dimensions):
            table[key] = factors[v][key]
            paid_calls += 1
        return frozenset([v]), tuple(incidence[v]), table

    def merge(left, right):
        members_a, boundary_a, values_a = left
        members_b, boundary_b, values_b = right
        require(not members_a & members_b, 'overlapping tensor blocks')
        shared = tuple(sorted(set(boundary_a) & set(boundary_b)))
        outside = tuple(sorted(set(boundary_a) ^ set(boundary_b)))
        output = {}
        for key in assignments(outside,dimensions):
            fixed = dict(zip(outside,key))
            value = ZERO
            for inner in assignments(shared,dimensions):
                all_values = fixed | dict(zip(shared,inner))
                a = values_a[tuple(all_values[e] for e in boundary_a)]
                b = values_b[tuple(all_values[e] for e in boundary_b)]
                value = add(value,multiply(a,b))
            output[key] = value
        return members_a | members_b, outside, output

    def build(block):
        if len(block) == 1:
            return leaf(block[0])
        cut = len(block)//2
        return merge(build(block[:cut]),build(block[cut:]))

    block_tables = [build(block) for block in plan]
    final_edges = tuple(sorted(set().union(*(set(t[1]) for t in block_tables))))
    total = ZERO
    for values in assignments(final_edges,dimensions):
        assignment = dict(zip(final_edges,values))
        term = ONE
        for _, boundary, table in block_tables:
            term = multiply(term,table[tuple(assignment[e] for e in boundary)])
        total = add(total,term)
    return total, paid_calls


def main():
    c = json.loads((ROOT/'data/support_consistency_certificate.json').read_text())
    plans = c['plans']
    random_source = random.Random(20261026)
    cases, comparisons, nonzero, selected = 0, 0, 0, [0]*9
    for number in range(32):
        dimensions = [1]*45
        active = random_source.sample(range(45), number % 11)
        for edge in active:
            dimensions[edge] = 2
        edges, incidence, factors = fixture(dimensions,random_source,zero_factor=(number%9 == 0))
        reference = direct(dimensions,incidence,factors)
        nonzero += reference != ZERO
        expected_calls = sum(prod(dimensions[e] for e in boundary) for boundary in incidence)
        results = []
        for plan in plans:
            value, calls = evaluate_plan(plan,dimensions,edges,incidence,factors)
            require(value == reference,'regrouping differs from exhaustive sum')
            require(calls == expected_calls,'recursive singleton calls not fully charged')
            results.append(value)
            comparisons += 1
        j, scores = joint_selector(plans,dimensions)
        require(results[j] == reference and scores[j] == min(scores),'joint selector')
        selected[j] += 1
        cases += 1
    require(nonzero > 0,'vacuous all-zero fixtures')
    dimensions = [1]*45
    edges, incidence, factors = fixture(dimensions,random_source)
    dimensions[0] = 0
    require(evaluate_plan(plans[0],dimensions,edges,incidence,factors) == (ZERO,0),
            'empty list must contribute zero without entry calls')
    errors = 0
    for bad in [[-1]+[1]*44, [3]+[1]*44]:
        try:
            joint_selector(plans,bad)
        except ValueError:
            errors += 1
    require(errors == 2,'invalid selector input accepted')
    try:
        bad = [list(block) for block in plans[0]]
        bad[0][0] = bad[0][1]
        plan_data(10,bad)
    except ValueError:
        errors += 1
    require(errors == 3,'invalid plan accepted')
    print(json.dumps({'status':'PASS','ring':'(Z/64Z)[e]/(e^2)',
                      'fixtures':cases,'all_plan_reference_comparisons':comparisons,
                      'nonzero_reference_values':nonzero,'selected_plan_counts':selected,
                      'paid_singleton_entry_counts_checked':comparisons,
                      'empty_list_control':'PASS','invalid_input_controls_rejected':errors,
                      'scope':'exact regrouping and joint selector; scalar backend only'},indent=2))


if __name__ == '__main__':
    main()
