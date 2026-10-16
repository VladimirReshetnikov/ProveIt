#!/usr/bin/env python3
"""Exact EPSC formula counts and finite checks for the native-rule proposal.

This is not a proof checker or a consistency test. The universal proofs are
in closure_rule_notes.md. Formula constructors and finite semantics here are
independent of the repository's implementation.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path


def atom(x, y):
    return ("E", x, y)


def hole(x, y):
    return ("R", x, y)


BOT = ("bottom",)


def imp(p, q):
    return ("implies", p, q)


def every(x, p):
    return ("forall", x, p)


def neg(p):
    return imp(p, BOT)


def some(x, p):
    return neg(every(x, neg(p)))


def both(p, q):
    return neg(imp(p, neg(q)))


def either(p, q):
    return imp(neg(p), q)


def sub(x, y, z):
    return every(z, imp(atom(z, x), atom(z, y)))


def empty(x, z):
    return every(z, neg(atom(z, x)))


def endpoints(*, curried=True, factored=False):
    """Use x=0,y=1,b=2,z=3. Reuse private b as the hull variable."""
    x, y, b, z = 0, 1, 2, 3
    rho = hole(x, y)
    bound = every(x, some(b, every(y, imp(rho, sub(y, b, z)))))
    active = either(empty(x, z), atom(x, b))
    step = (imp(active, imp(rho, atom(y, b))) if curried else
            imp(both(active, rho), atom(y, b)))
    support = imp(atom(y, b), some(x, rho))
    if factored:
        body = every(y, both(every(x, step), support))
    else:
        body = both(every(x, every(y, step)), every(y, support))
    hull = some(b, body)
    return bound, hull


def count(formula):
    counts = Counter()
    pending = [formula]
    while pending:
        f = pending.pop()
        counts[f[0]] += 1
        if f[0] == "implies":
            pending.extend((f[1], f[2]))
        elif f[0] == "forall":
            pending.append(f[2])
    return {"nodes": sum(counts.values()), "constructors": dict(sorted(counts.items()))}


def evaluate(formula, n, membership, relation, env=None):
    a = {} if env is None else env
    kind = formula[0]
    if kind == "bottom":
        return False
    if kind in ("E", "R"):
        graph = membership if kind == "E" else relation
        return bool(graph & (1 << (a[formula[1]] * n + a[formula[2]])))
    if kind == "implies":
        return (not evaluate(formula[1], n, membership, relation, a) or
                evaluate(formula[2], n, membership, relation, a))
    if kind == "forall":
        return all(evaluate(formula[2], n, membership, relation,
                            a | {formula[1]: value}) for value in range(n))
    raise ValueError(kind)


def fill_matrix(template, matrix):
    """Fill the canonical (0,1) hole without moving any existing binder.

    The examples below reserve 2,3 for the EPSC wrapper, 4 for its parameter,
    and 5 for the matrix's own local quantifier. Shadowing internal to the
    closed-except-for-4 boundedness guard is deliberate and harmless.
    """
    kind = template[0]
    if kind == "R":
        assert template[1:] == (0, 1)
        return matrix
    if kind == "implies":
        return imp(fill_matrix(template[1], matrix), fill_matrix(template[2], matrix))
    if kind == "forall":
        return every(template[1], fill_matrix(template[2], matrix))
    return template


def profiles(n, membership):
    return [sum(((membership >> (z * n + x)) & 1) << z for z in range(n))
            for x in range(n)]


def fibers(n, relation):
    mask = (1 << n) - 1
    return [(relation >> (x * n)) & mask for x in range(n)]


def direct_bound(n, prof, rows):
    for outputs in rows:
        union = 0
        for y in range(n):
            if outputs & (1 << y):
                union |= prof[y]
        if not any(union & ~bound == 0 for bound in prof):
            return False
    return True


def direct_hull(n, prof, rows, *, support=True, activate_empty=True):
    output_range = 0
    for row in rows:
        output_range |= row
    for hull in prof:
        if support and hull & ~output_range:
            continue
        if all(not ((activate_empty and prof[x] == 0) or hull & (1 << x))
               or rows[x] & ~hull == 0 for x in range(n)):
            return True
    return False


def check(max_n=3):
    if max_n not in (1, 2, 3):
        raise ValueError("max_n must be 1, 2 or 3")
    formula_counts = {}
    variants = [(False, False, "uncurried"), (True, False, "curried"),
                (True, True, "curried_common_forall")]
    for curried, factored, name in variants:
        b, h = endpoints(curried=curried, factored=factored)
        formula_counts[name] = {
            "bound": count(b), "hull": count(h),
            "axiom": count(imp(b, h)),
            "rule_endpoints_nodes": count(b)["nodes"] + count(h)["nodes"],
        }
    assert [formula_counts[s]["axiom"]["nodes"] for s in
            ("uncurried", "curried", "curried_common_forall")] == [51, 47, 46]

    # Compare actual expanded syntax with an independent bit-set evaluator.
    # Three labels suffice for the parameter-closure counterexample below;
    # exhaustive AST checks only use n<=2 to avoid redundant slow evaluation.
    ast_cases = 0
    direct_cases = 0
    guard_cases = 0
    two_instance_russell_cases = 0
    formulas = [endpoints(curried=a, factored=b) for a, b, _ in variants]
    for n in range(1, max_n + 1):
        for membership in range(1 << (n * n)):
            prof = profiles(n, membership)
            russell = sum((not bool(prof[y] & (1 << y))) << y
                          for y in range(n))
            assert not (direct_hull(n, prof, [0] * n) and
                        direct_hull(n, prof, [russell] * n))
            two_instance_russell_cases += 1
            for relation in range(1 << (n * n)):
                rows = fibers(n, relation)
                bounded = direct_bound(n, prof, rows)
                hull = direct_hull(n, prof, rows)
                guarded = rows if bounded else [0] * n
                assert direct_bound(n, prof, guarded)
                guarded_hull = direct_hull(n, prof, guarded)
                assert not (guarded_hull and bounded) or hull
                if bounded:
                    assert guarded_hull == hull
                guard_cases += 1
                direct_cases += 1
                if n <= 2:
                    for b, h in formulas:
                        assert evaluate(b, n, membership, relation) == bounded
                        assert evaluate(h, n, membership, relation) == hull
                        ast_cases += 2

    # If support is dropped, the universal one-element membership structure
    # satisfies the remaining schema, for both possible binary matrices.
    assert all(not direct_bound(1, [1], rows) or
               direct_hull(1, [1], rows, support=False)
               for rows in ([0], [1]))
    # If all initial activation is dropped, the one-element empty structure
    # chooses the empty hull for every possible matrix.
    assert all(not direct_bound(1, [0], rows) or
               direct_hull(1, [0], rows, activate_empty=False)
               for rows in ([0], [1]))

    # Wrong parameter guard: UC_p B_rho instead of the required open B_rho(p).
    # Domain={0,1,2}, membership={(1,1),(2,2)}. Object0 is empty, but belongs
    # to no object. The constant0 matrix is bounded and has no EPSC hull.
    # The constant{1,2} matrix has no subset bound for its outputs.
    n = 3
    membership = (1 << 4) | (1 << 8)
    prof = profiles(n, membership)
    # This family is definable in the original one-relation equality-free
    # language by rho(x,y;p) := (epsilon(p) iff epsilon(y)); x is unused.
    family = [[1] * n, [6] * n, [6] * n]
    ep, ey = empty(4, 5), empty(1, 5)
    parameter_matrix = either(both(ep, ey), both(neg(ep), neg(ey)))
    for p in range(n):
        for x in range(n):
            row = sum(int(evaluate(parameter_matrix, n, membership, 0,
                                   {0: x, 1: y, 4: p})) << y
                      for y in range(n))
            assert row == family[p][x]
    bounded_values = [direct_bound(n, prof, r) for r in family]
    hull_values = [direct_hull(n, prof, r) for r in family]
    global_guard = all(bounded_values)
    guarded_hulls = [direct_hull(n, prof, r if global_guard else [0] * n)
                     for r in family]
    assert bounded_values == [True, False, False]
    assert hull_values == [False, False, False]
    assert guarded_hulls == [True, True, True]
    assert not all(not b or h for b, h in zip(bounded_values, hull_values))

    # Check this delicate parameter example using the *fully expanded* AST,
    # including the nested bound formula in the guard. This exercises the
    # legal shadowing when wrapper labels are reused inside that guard.
    bt, ht = endpoints(curried=True, factored=True)
    br = fill_matrix(bt, parameter_matrix)
    hr = fill_matrix(ht, parameter_matrix)
    sigma = both(br, parameter_matrix)  # Correct: parameter4 remains free.
    bs = fill_matrix(bt, sigma)
    hs = fill_matrix(ht, sigma)
    sigma_wrong = both(every(4, br), parameter_matrix)
    hs_wrong = fill_matrix(ht, sigma_wrong)
    expanded_values = []
    for p in range(n):
        values = [evaluate(f, n, membership, 0, {4: p})
                  for f in (br, hr, bs, hs, hs_wrong)]
        assert values == [bounded_values[p], hull_values[p], True,
                          False if p == 0 else True, True]
        expanded_values.append(values)
    wanted_axiom = every(4, imp(br, hr))
    correct_transport = imp(every(4, hs), wanted_axiom)
    incorrect_transport = imp(every(4, hs_wrong), wanted_axiom)
    assert evaluate(correct_transport, n, membership, 0)
    assert not evaluate(incorrect_transport, n, membership, 0)

    return {
        "status": "PASS",
        "scope": "Formula counts, exact finite semantic comparisons and one explicit counterexample; not a proof checker or a consistency test.",
        "max_domain": max_n,
        "formula_counts": formula_counts,
        "all_graph_matrix_pairs": direct_cases,
        "expanded_AST_comparisons": ast_cases,
        "guard_lemma_regressions": guard_cases,
        "two_instance_unbounded_EPSC_Russell_regressions": two_instance_russell_cases,
        "deleted_support_universal_one_point_model": True,
        "deleted_activation_empty_one_point_model": True,
        "wrong_universal_parameter_guard_counterexample": {
            "domain": [0, 1, 2], "membership_edges": [[1, 1], [2, 2]],
            "formula": "rho(x,y;p) := epsilon(p) iff epsilon(y)",
            "parameter_fibers": [[[0]] * n, [[1, 2]] * n, [[1, 2]] * n],
            "bounded_values": bounded_values, "hull_values": hull_values,
            "globally_guarded_hull_values": guarded_hulls,
            "expanded_AST_columns": ["B_rho", "H_rho", "B_sigma_correct",
                                     "H_sigma_correct", "H_sigma_wrong_global"],
            "expanded_AST_values_by_parameter": expanded_values,
            "correct_expanded_transport": True,
            "incorrect_expanded_transport": False,
        },
    }


def main():
    if not __debug__:
        raise SystemExit("Assertions must be enabled.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=3)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = check(args.max_n)
    serialized = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(serialized)
    print(serialized)


if __name__ == "__main__":
    main()
