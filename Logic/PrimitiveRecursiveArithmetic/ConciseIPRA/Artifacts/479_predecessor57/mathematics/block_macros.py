"""Finite selector construction and exact raw-tree accounting.

Untrusted research utility.  It uses ramp58.py for explicit scalar ASTs and
does not import any proof checker.  Numerical checks do not prove the native
derivability statements; those have separate written proofs.
"""
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
import predecessor57 as arithmetic

Z = arithmetic.ZERO
V = arithmetic.var
S = arithmetic.suc
I = arithmetic.iterator
C = arithmetic.select
fresh = arithmetic.fresh


def equation(s, t):
    return ("=", s, t)


def paired(x, y, formula):
    return ("D", x, y, formula)


def substitute(tree, name, term):
    tag = tree[0]
    if tag == "v":
        return term if tree[1] == name else tree
    if tag == "0":
        return tree
    if tag == "S":
        return S(substitute(tree[1], name, term))
    if tag == "I":
        _, n, a, bound, body = tree
        return ("I", substitute(n, name, term), substitute(a, name, term),
                bound, body if bound == name else substitute(body, name, term))
    if tag == "=":
        return equation(substitute(tree[1], name, term),
                        substitute(tree[2], name, term))
    if name in tree[1:3]:
        return tree
    return paired(tree[1], tree[2], substitute(tree[3], name, term))


def gate(control, formula):
    if formula[0] == "=":
        return equation(C(control, Z, formula[1]), C(control, Z, formula[2]))
    return paired(formula[1], formula[2], gate(control, formula[3]))


def align(formula, x, y):
    return substitute(substitute(formula[3], formula[1], V(x)),
                      formula[2], V(y))


def mix(control, first, second):
    if first[0] == second[0] == "=":
        return equation(C(control, first[1], second[1]),
                        C(control, first[2], second[2]))
    x, y = fresh(), fresh()
    left = align(first, x, y) if first[0] == "D" else gate(V(y), first)
    right = align(second, x, y) if second[0] == "D" else gate(V(y), second)
    return paired(x, y, mix(control, left, right))


def let_formula(name, seed, formula):
    if formula[0] == "=":
        return equation(
            I(S(Z), seed, lambda u: substitute(formula[1], name, u)),
            I(S(Z), seed, lambda u: substitute(formula[2], name, u)))
    return paired(formula[1], formula[2], let_formula(name, seed, formula[3]))


def finite_selector(control, formulas):
    if len(formulas) == 1:
        return formulas[0]
    w = fresh()
    tail = finite_selector(V(w), formulas[1:])
    tail = let_formula(w, arithmetic.ramp_new(control), tail)
    return mix(arithmetic.parity(control), tail, formulas[0])


def flat_block(formulas, existential):
    ordered = sorted(formulas, key=rank, reverse=True)
    x, y = fresh(), fresh()
    control = V(x) if existential else V(y)
    return paired(x, y, gate(V(y), finite_selector(control, ordered)))


def conjunction(first, second):
    x, y = fresh(), fresh()
    return paired(x, y, gate(V(y), mix(arithmetic.parity(V(y)), first, second)))


def disjunction(first, second):
    x, y = fresh(), fresh()
    return paired(x, y, gate(V(y), mix(V(x), first, second)))


def balanced(formulas, binary):
    if len(formulas) == 1:
        return formulas[0]
    middle = len(formulas) // 2
    return binary(balanced(formulas[:middle], binary),
                  balanced(formulas[middle:], binary))


def universal(name, formula, predecessor):
    x, y = fresh(), fresh()
    return paired(x, y, gate(V(y), substitute(formula, name, predecessor(V(y)))))


def formula_size(formula):
    if formula[0] == "=":
        return 1 + arithmetic.size(formula[1]) + arithmetic.size(formula[2])
    return 1 + formula_size(formula[3])


def rank(formula):
    return 0 if formula[0] == "=" else 1 + rank(formula[3])


def payload(formula):
    return formula_size(formula) - rank(formula) - 1


def free_formula(formula):
    if formula[0] == "=":
        return arithmetic.free(formula[1]) | arithmetic.free(formula[2])
    return free_formula(formula[3]) - set(formula[1:3])


def numeral(n):
    t = Z
    for _ in range(n):
        t = S(t)
    return t


def example_formula(index, depth):
    formula = equation(V("a" + str(index)), Z)
    for _ in range(depth):
        x, y = fresh(), fresh()
        # Dependence on y prevents this syntactic family from being just a
        # sequence of vacuous D wrappers.  No theorem status is asserted.
        formula = paired(x, y, gate(V(y), formula))
    return formula


def prefix_matrix(n):
    t = Z
    for j in reversed(range(n)):
        t = arithmetic.add(t, V("x" + str(j)))
    return equation(t, S(Z))


def minimum_padding(ranks):
    @lru_cache(None)
    def top(mask):
        return max(ranks[j] for j in range(len(ranks)) if mask >> j & 1)

    @lru_cache(None)
    def solve(mask):
        if mask & (mask - 1) == 0:
            return 0
        first = mask & -mask
        best = None
        left = (mask - 1) & mask
        while left:
            right = mask ^ left
            if right and left & first:
                cost = solve(left) + solve(right) + abs(top(left) - top(right))
                best = cost if best is None else min(best, cost)
            left = (left - 1) & mask
        return best

    return solve((1 << len(ranks)) - 1)


def require(condition, description):
    if not condition:
        raise ValueError(description)


def main():
    size_checks = 0
    for n in (1, 2, 3, 4, 8, 16, 32, 64):
        for shift in range(5):
            formulas = [example_formula(j, (3 * j + shift) % 6) for j in range(n)]
            r = max(map(rank, formulas))
            low = min(map(rank, formulas))
            expected = sum(map(payload, formulas)) + 66 * (n - 1) + 6 * (r - low) + r + 8
            for existential in (False, True):
                block = flat_block(formulas, existential)
                require(rank(block) == r + 1, "flat rank")
                require(formula_size(block) == expected, "flat size")
                require(free_formula(block) == frozenset("a" + str(j) for j in range(n)),
                        "flat scope")
                size_checks += 1

    row_checks = 0
    for n in range(1, 7):
        formulas = [equation(numeral(j), Z) for j in range(n)]
        selector = finite_selector(V("z"), formulas)
        require(selector[0] == "=", "rank-zero selector")
        for j in range(n):
            left = arithmetic.evaluate(selector[1], {"z": 2 ** j})
            right = arithmetic.evaluate(selector[2], {"z": 2 ** j})
            require((left, right) == (j, 0), ("selector row", n, j, left, right))
            row_checks += 1

    padding_checks = 0
    for n in range(1, 6):
        for ranks in product(range(4), repeat=n):
            require(minimum_padding(ranks) == max(ranks) - min(ranks), ranks)
            padding_checks += 1

    prefix_rows = []
    for n in (1, 2, 4, 8, 16, 32):
        old, new = prefix_matrix(n), prefix_matrix(n)
        for j in reversed(range(n)):
            old = universal("x" + str(j), old,
                            lambda t: arithmetic.predecessor(t, arithmetic.ramp_old))
            new = universal("x" + str(j), new, arithmetic.predecessor57)
        require(formula_size(old) == 85 * n + 4, "old universal count")
        require(formula_size(new) == 67 * n + 4, "new universal count")
        require(rank(new) == rank(old) == n, "universal rank")
        require(not free_formula(old) and not free_formula(new), "universal scope")
        prefix_rows.append(dict(n=n, old_nodes=formula_size(old),
                                new_nodes=formula_size(new), paired_rank=n))

    comparison = []
    for n in (2, 4, 8, 16, 32):
        formulas = [example_formula(j, 0) for j in range(n)]
        old_and = balanced(formulas, conjunction)
        old_or = balanced(formulas, disjunction)
        new_and = flat_block(formulas, False)
        new_or = flat_block(formulas, True)
        comparison.append(dict(
            operands=n, balanced_rank=rank(old_and), flat_rank=rank(new_and),
            balanced_conjunction_nodes=formula_size(old_and),
            balanced_disjunction_nodes=formula_size(old_or),
            flat_conjunction_nodes=formula_size(new_and),
            flat_disjunction_nodes=formula_size(new_or)))
    result = {
        "status": "finite checks passed; not a proof-assistant verification",
        "flat_size_and_scope_cases": size_checks,
        "literal_scalar_selector_rows": row_checks,
        "exhaustive_small_padding_cases": padding_checks,
        "selector_branch_overhead": 66,
        "padding_counterexample": {
            "operand_ranks": [0, 1, 2, 3],
            "balanced_pairing_padding_levels": 4,
            "optimal_padding_levels": 3,
        },
        "universal_prefix_actual_AST_counts": prefix_rows,
        "rank_vs_size_comparison": comparison,
        "scope": "Native Eq/D trees before compact guarded-public embedding.",
    }
    Path(__file__).with_name("block_macros_results.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
