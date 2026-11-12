"""Expanded scalar trees for the absorbing-factor predecessor.

Untrusted research utility: finite evaluations are examples, not an iPRA
proof. The internal equational proof is in predecessor50_detailed.tex.
The original and 57-node controls implement the displayed definitions in
ProveIt/ConciseIPRA and its incoming ipra_479_predecessor57 package.
No zero test, parity, selector, addition, or arithmetic macro is primitive
in a measured tree. Repeated subtrees count at every occurrence.
"""

from functools import lru_cache
from itertools import count
import json
from pathlib import Path


_serial = count()
ZERO = ("zero",)


def var(name):
    return ("var", name)


def suc(term):
    return ("suc", term)


def it(counter, seed, make_body):
    name = "u" + str(next(_serial))
    return ("it", counter, seed, name, make_body(var(name)))


def select(counter, first, second):
    return it(counter, first, lambda _: second)


def add(a, b):
    return it(b, a, suc)


def zero_test(n):
    return select(n, suc(ZERO), ZERO)


def parity(n):
    return it(n, ZERO, zero_test)


def short_clock(n):
    return it(n, ZERO, lambda u: it(u, suc(suc(ZERO)), zero_test))


def short_ramp(n):
    return it(n, ZERO, lambda u: suc(select(short_clock(u), suc(u), u)))


def old_clock(n):
    return it(n, ZERO, lambda u: add(zero_test(u), add(parity(u), parity(u))))


def old_ramp(n):
    return it(n, ZERO, lambda u: suc(add(u, old_clock(u))))


def power_two(n):
    return it(n, suc(ZERO), lambda u: add(u, u))


def factor_old(n):
    return select(parity(n), old_ramp(n), n)


def factor_short(n):
    return select(parity(n), short_ramp(n), n)


def factor_absorbing(n):
    return select(parity(n), short_ramp(n), ZERO)


def weighted_parity(n):
    return it(n, ZERO, lambda v: select(v, n, ZERO))


def factor_weighted(n):
    return select(weighted_parity(n), short_ramp(n), ZERO)


def old_compare(x, y):
    return parity(it(y, power_two(x), factor_old))


def short_compare(x, y):
    return parity(it(y, power_two(x), factor_short))


def absorbing_compare(x, y):
    return zero_test(it(suc(y), power_two(x), factor_absorbing))


def predecessor75(n):
    return it(n, ZERO, lambda u:
              select(old_compare(suc(suc(u)), n), u, suc(u)))


def predecessor57(n):
    return it(n, ZERO, lambda u:
              select(short_compare(n, suc(u)), suc(u), u))


def predecessor55(n):
    return it(n, ZERO, lambda u:
              select(absorbing_compare(n, suc(u)), suc(u), u))


def predecessor51(n):
    return it(n, ZERO, lambda u:
              select(it(suc(suc(u)), power_two(n), factor_absorbing), u, suc(u)))


def predecessor50(n):
    return it(n, ZERO, lambda u:
              select(it(suc(suc(u)), power_two(n), factor_weighted), u, suc(u)))


def nodes(term):
    if term[0] in ("zero", "var"):
        return 1
    if term[0] == "suc":
        return 1 + nodes(term[1])
    return 1 + nodes(term[1]) + nodes(term[2]) + nodes(term[4])


@lru_cache(None)
def free_variables(term):
    if term[0] == "zero":
        return frozenset()
    if term[0] == "var":
        return frozenset((term[1],))
    if term[0] == "suc":
        return free_variables(term[1])
    return (free_variables(term[1]) | free_variables(term[2]) |
            (free_variables(term[4]) - {term[3]}))


def evaluate(term, environment):
    assignment = tuple(sorted((name, environment[name])
                              for name in free_variables(term)))
    return _evaluate(term, assignment)


@lru_cache(None)
def _evaluate(term, assignment):
    env = dict(assignment)
    kind = term[0]
    if kind == "zero":
        return 0
    if kind == "var":
        return env[term[1]]
    if kind == "suc":
        return evaluate(term[1], env) + 1
    _, counter, seed, bound, body = term
    total = evaluate(counter, env)
    value = evaluate(seed, env)
    for _ in range(total):
        env[bound] = value
        value = evaluate(body, env)
    return value


def substitute(tree, name, term):
    kind = tree[0]
    if kind == "var":
        return term if tree[1] == name else tree
    if kind == "zero":
        return tree
    if kind == "suc":
        return suc(substitute(tree[1], name, term))
    if kind == "eq":
        return ("eq", substitute(tree[1], name, term),
                substitute(tree[2], name, term))
    if kind == "D":
        return tree if name in tree[1:3] else (
            "D", tree[1], tree[2], substitute(tree[3], name, term))
    return ("it", substitute(tree[1], name, term),
            substitute(tree[2], name, term), tree[3],
            tree[4] if tree[3] == name else substitute(tree[4], name, term))


def gate(control, formula):
    if formula[0] == "eq":
        return ("eq", select(control, ZERO, formula[1]),
                select(control, ZERO, formula[2]))
    return ("D", formula[1], formula[2], gate(control, formula[3]))


def formula_nodes(formula):
    if formula[0] == "eq":
        return 1 + nodes(formula[1]) + nodes(formula[2])
    return 1 + formula_nodes(formula[3])


def prefix_example(length, predecessor):
    term = ZERO
    for j in reversed(range(length)):
        term = add(term, var("x" + str(j)))
    formula = ("eq", term, suc(ZERO))
    for j in reversed(range(length)):
        witness, counter = "a" + str(next(_serial)), "b" + str(next(_serial))
        formula = ("D", witness, counter,
                   gate(var(counter), substitute(formula, "x" + str(j),
                                                  predecessor(var(counter)))))
    return formula


def main():
    n, x, y = map(var, ("n", "x", "y"))
    terms = {
        "original_predecessor": predecessor75(n),
        "incoming_predecessor": predecessor57(n),
        "absorbing_predecessor_before_fusion": predecessor55(n),
        "absorbing_predecessor51": predecessor51(n),
        "absorbing_predecessor50": predecessor50(n),
        "short_clock": short_clock(n),
        "short_ramp": short_ramp(n),
        "absorbing_factor": factor_absorbing(n),
        "weighted_parity": weighted_parity(n),
        "weighted_factor": factor_weighted(n),
        "power_two": power_two(n),
        "absorbing_comparator": absorbing_compare(x, y),
    }
    expected = dict(original_predecessor=75, incoming_predecessor=57,
                    absorbing_predecessor_before_fusion=55,
                    absorbing_predecessor51=51, absorbing_predecessor50=50, short_clock=13,
                    short_ramp=21, absorbing_factor=31, power_two=9,
                    absorbing_comparator=47, weighted_parity=7, weighted_factor=30)
    counts = {name: nodes(term) for name, term in terms.items()}
    assert counts == expected, (counts, expected)
    for name, term in terms.items():
        assert free_variables(term) == ({"x", "y"} if name.endswith("comparator") else {"n"})

    raw_values = {}
    for name in ("incoming_predecessor", "absorbing_predecessor_before_fusion",
                 "absorbing_predecessor51", "absorbing_predecessor50"):
        values = [evaluate(terms[name], {"n": i}) for i in range(7)]
        assert values == [0, 0, 1, 2, 3, 4, 5], (name, values)
        raw_values[name] = values

    # Direct numerical observations are separate from raw-tree evaluation.
    def factor(k):
        return 0 if k % 2 else 3 * k // 2

    def iterate(k, seed):
        for _ in range(k):
            seed = factor(seed)
        return seed

    checks = 0
    for a in range(1001):
        assert factor(2 * a) == 3 * a
        assert factor(3 * a) == 3 * factor(a)
        checks += 2
    for a in range(17):
        for b in range(17):
            assert int(iterate(b + 1, 2 ** a) == 0) == int(a <= b)
            checks += 1
    assert factor(0) == factor(1) == 0
    checks += 1

    weighted_values = [evaluate(terms["weighted_parity"], {"n": i}) for i in range(33)]
    assert weighted_values == [i if i % 2 else 0 for i in range(33)]
    for i, test in enumerate(weighted_values):
        for a in range(7):
            for b in range(7):
                assert (a if test == 0 else b) == (a if i % 2 == 0 else b)
                checks += 1

    prefix_rows = []
    for k in (1, 2, 4, 8, 10, 16, 32):
        before = formula_nodes(prefix_example(k, predecessor57))
        after = formula_nodes(prefix_example(k, predecessor50))
        assert before == 67 * k + 4 and after == 60 * k + 4
        prefix_rows.append({"variables": k, "previous_nodes": before,
                            "new_nodes": after})

    result = {
        "status": "constructor counts and finite examples passed",
        "proof_status": "internal equational proof in accompanying TeX; no Lean/Rocq formalization claimed",
        "metric": "fully expanded raw 0/S/I constructor nodes, one per variable/zero/constructor",
        "term_nodes": counts,
        "raw_tree_predecessor_values_at_0_through_6": raw_values,
        "fast_numerical_identity_checks": checks,
        "weighted_parity_values_at_0_through_32": weighted_values,
        "reduction_from_incoming57": {"saved_nodes": 7, "fraction": "7/57"},
        "reduction_from_original75": {"saved_nodes": 25, "fraction": "25/75"},
        "universal_prefix_formula_family": prefix_rows,
        "universal_prefix_check": "actual expanded formula trees constructed; no formula-only size substitution",
        "expanded_predecessor_ast": terms["absorbing_predecessor50"],
    }
    destination = Path(__file__).with_name("predecessor50_results.json")
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items()
                      if key != "expanded_predecessor_ast"}, indent=2))


if __name__ == "__main__":
    main()
