#!/usr/bin/env python3
"""Independent literal-sum tests for exact affine selection and reassociation."""
import json
import random
from itertools import combinations, product
from math import prod
from affine_modes import EDGES, PLANS, contract, select_plan


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def direct(dimensions, values, add, multiply, zero, one):
    total = zero
    incident = [tuple(e for e in EDGES if g in e) for g in range(9)]
    positions = [{e: i for i, e in enumerate(EDGES)} for _ in range(9)]
    for state in product(*(range(dimensions[e]) for e in EDGES)):
        term = one
        for g in range(9):
            local = tuple(state[positions[g][e]] for e in incident[g])
            term = multiply(term, values[g][local])
        total = add(total, term)
    return total


def independent_scores(dimensions):
    # Independent score evaluation using dimension products for three classes,
    # without reading any support vector from the implementation.
    result = []
    for plan in PLANS:
        ops = []
        for a, b, c in plan:
            ops.extend([((b,), (c,), tuple(x for x in range(9) if x not in (b,c))),
                        ((a,), (b,c), tuple(x for x in range(9) if x not in (a,b,c)))])
        ops.append(plan)
        scores = []
        for op in ops:
            pp = [prod(dimensions[tuple(sorted((x,y)))] for x in op[a] for y in op[b])
                  for a,b in combinations(range(3),2)]
            scores.append(max(pp[j]**2 * prod(pp[k]**5 for k in range(3) if k != j)
                              for j in range(3)))
        boundary = [(x,) for x in range(9)] + [bb[1:] for bb in plan] + list(plan)
        ps = max(prod(v for e, v in dimensions.items() if (e[0] in bb) != (e[1] in bb))
                 for bb in boundary)
        # Independent ceiling logarithm via exact powers of two.
        def ceiling_log(n):
            k = 0
            power = 1
            while power < n:
                power *= 2
                k += 1
            return k
        aa, bb = ceiling_log(max(scores)), ceiling_log(ps)
        result.append(max(7*aa*aa, 225*bb*bb))
    return result


def run():
    rng = random.Random(269103)
    cases = 0
    contractions = 0
    child_calls = 0
    maximum_global_domain = 0
    nonzero_fixtures = 0
    modulus = 64
    # Nonfield ring (Z/64Z)[epsilon]/(epsilon^2).
    add = lambda x,y: ((x[0]+y[0])%modulus, (x[1]+y[1])%modulus)
    mul = lambda x,y: ((x[0]*y[0])%modulus,
                      (x[0]*y[1]+x[1]*y[0])%modulus)
    zero = (0,0); one = (1,0)
    for trial in range(72):
        dimensions = {e: 1 for e in EDGES}
        for e in rng.sample(list(EDGES), trial % 8):
            dimensions[e] = 2 if trial % 3 else 3
        incident = [tuple(e for e in EDGES if g in e) for g in range(9)]
        values = []
        for g in range(9):
            vv = {}
            for state in product(*(range(dimensions[e]) for e in incident[g])):
                # Include zero-divisor and nilpotent entries; not just units.
                vv[state] = (rng.randrange(64), rng.randrange(64))
            values.append(vv)
        original = direct(dimensions, values, add, mul, zero, one)
        nonzero_fixtures += original != zero
        ss = independent_scores(dimensions)
        chosen = min(range(4), key=lambda i: (ss[i], i))
        require(select_plan(dimensions)["chosen_plan"] == chosen, "Exact selector mismatch")
        calls_seen = [0]*9
        def oracle(g, axes, state):
            require(axes == incident[g], "Oracle axis order mismatch")
            calls_seen[g] += 1
            return values[g][state]
        for forced in (None,0,1,2,3):
            calls_seen[:] = [0]*9
            result, receipt = contract(dimensions, oracle, zero, one, add, mul, forced)
            require(result == original, "Tree contraction disagrees with literal sum")
            expected = [len(vv) for vv in values]
            require(receipt["group_calls"] == expected == calls_seen,
                    "Unpaid/repeated child calls")
            child_calls += sum(calls_seen)
            contractions += 1
        cases += 1
        maximum_global_domain = max(maximum_global_domain, prod(dimensions.values()))
    # Empty domains contribute zero and must not call a group oracle.
    dimensions = {e: 1 for e in EDGES}; dimensions[EDGES[0]] = 0
    def forbidden(*args):
        raise RuntimeError("An empty domain called the group oracle")
    require(contract(dimensions, forbidden, zero, one, add, mul)[0] == zero,
            "Empty-domain contraction incorrect")
    negatives = 0
    for replacement in (-1, 1.25, True):
        bad = {e: 1 for e in EDGES};bad[EDGES[0]] = replacement
        try:select_plan(bad)
        except ValueError:negatives += 1
        else:raise RuntimeError("Invalid dimension accepted")
    try:select_plan(dimensions)
    except ValueError:negatives += 1
    else:raise RuntimeError("Empty domain accepted by selector")
    bad = {e: 1 for e in EDGES};del bad[EDGES[0]]
    try:select_plan(bad)
    except ValueError:negatives += 1
    else:raise RuntimeError("Incomplete dimension table accepted")
    # Exact arithmetic check that the test ring really has nonzero nilpotents.
    require(mul((0,1),(0,1)) == zero and (0,1) != zero, "Ring fixture is not nilpotent")
    require(nonzero_fixtures > 0, "All reference answers vanished; fixtures are inadequate")
    ceiling_checks = 0
    for k in (0,1,2,8,64,511,4096):
        for n in {max(1,(1 << k)-1), 1 << k, (1 << k)+1}:
            ceiling = (n-1).bit_length()
            require((1 << ceiling) >= n and (ceiling == 0 or (1 << (ceiling-1)) < n),
                    "Integer ceiling logarithm incorrect")
            ceiling_checks += 1
    return {"status":"PASS", "fixture_count":cases,
            "literal_comparisons":contractions, "paid_group_calls":child_calls,
            "largest_global_domain":maximum_global_domain, "negative_controls":negatives,
            "nonzero_answer_fixtures":nonzero_fixtures,
            "ceiling_logarithm_boundary_checks":ceiling_checks,
            "ring":"(Z/64Z)[epsilon]/(epsilon^2)",
            "selector":"max(7*ceil_log2(Ptime)^2, 225*ceil_log2(Pspace)^2)",
            "empty_domain_without_oracle_calls":True,
            "fast_matrix_backend_implemented":False}

if __name__ == '__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
