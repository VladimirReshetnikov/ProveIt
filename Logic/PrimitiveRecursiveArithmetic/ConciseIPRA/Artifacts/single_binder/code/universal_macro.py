"""Exact native macro expansion and size comparison (untrusted research utility).

All arithmetic abbreviations, including predecessor, expand to 0, S, I.
This is not a proof checker and its finite checks do not establish the
metatheorem.  Names are globally fresh; size counts constructor nodes and
variable/zero leaves, not the number of characters in variable names.
"""
from functools import lru_cache
from itertools import count
import json
from pathlib import Path

serial = count()


def fresh():
    return "b" + str(next(serial))


def var(name):
    return ("v", name)


ZERO = ("0",)


def suc(term):
    return ("S", term)


def iterator(counter, initial, body):
    bound = fresh()
    return ("I", counter, initial, bound, body(var(bound)))


def selector(control, first, second):
    return iterator(control, first, lambda _: second)


def add(first, second):
    return iterator(second, first, suc)


def iszero(term):
    return selector(term, suc(ZERO), ZERO)


def parity(term):
    return iterator(term, ZERO, iszero)


def cycle3(term):
    return iterator(term, ZERO,
                    lambda u: add(iszero(u), add(parity(u), parity(u))))


def ramp(term):
    return iterator(term, ZERO, lambda u: suc(add(u, cycle3(u))))


def factor_map(term):
    return selector(parity(term), ramp(term), term)


def power2(term):
    return iterator(term, suc(ZERO), lambda u: add(u, u))


def leq_indicator(first, second):
    return parity(iterator(second, power2(first), factor_map))


def predecessor(term):
    """The finite term from certified_zero/reference/scalar_predecessor.tex."""
    return iterator(term, ZERO, lambda u:
                    selector(leq_indicator(suc(suc(u)), term), u, suc(u)))


def eq(left, right):
    return ("=", left, right)


def paired(x, y, body):
    return ("D", x, y, body)


def substitute(tree, name, image):
    """Capture-free here: generated binders are fresh for all supplied images."""
    kind = tree[0]
    if kind == "v":
        return image if tree[1] == name else tree
    if kind == "0":
        return tree
    if kind == "S":
        return suc(substitute(tree[1], name, image))
    if kind == "I":
        _, n, a, bound, h = tree
        return ("I", substitute(n, name, image), substitute(a, name, image),
                bound, h if bound == name else substitute(h, name, image))
    if kind == "=":
        return eq(substitute(tree[1], name, image),
                  substitute(tree[2], name, image))
    if kind == "D":
        return tree if name in tree[1:3] else paired(
            tree[1], tree[2], substitute(tree[3], name, image))
    raise ValueError(kind)


def gate(control, formula):
    if formula[0] == "=":
        return eq(selector(control, ZERO, formula[1]),
                  selector(control, ZERO, formula[2]))
    return paired(formula[1], formula[2], gate(control, formula[3]))


def align(formula, x, y):
    return substitute(substitute(formula[3], formula[1], var(x)),
                      formula[2], var(y))


def mix(control, first, second):
    """The inherited formula selector, with padding at unequal D ranks."""
    if first[0] == second[0] == "=":
        return eq(selector(control, first[1], second[1]),
                  selector(control, first[2], second[2]))
    x, y = fresh(), fresh()
    left = align(first, x, y) if first[0] == "D" else gate(var(y), first)
    right = align(second, x, y) if second[0] == "D" else gate(var(y), second)
    return paired(x, y, mix(control, left, right))


def conjunction(first, second):
    x, y = fresh(), fresh()
    return paired(x, y, gate(var(y), mix(parity(var(y)), first, second)))


def universal_old(name, matrix):
    x, y = fresh(), fresh()
    positive = paired(x, y, gate(var(y), substitute(matrix, name, var(y))))
    return conjunction(substitute(matrix, name, ZERO), positive)


def universal_new(name, matrix):
    x, y = fresh(), fresh()
    return paired(x, y, gate(var(y), substitute(matrix, name, predecessor(var(y)))))


def size(tree):
    kind = tree[0]
    if kind in ("0", "v"):
        return 1
    if kind == "S":
        return 1 + size(tree[1])
    if kind in ("=",):
        return 1 + size(tree[1]) + size(tree[2])
    if kind == "I":
        return 1 + size(tree[1]) + size(tree[2]) + size(tree[4])
    return 1 + size(tree[3])


def rank(formula):
    return 0 if formula[0] == "=" else 1 + rank(formula[3])


def payload(formula):
    while formula[0] == "D":
        formula = formula[3]
    return size(formula) - 1


@lru_cache(None)
def free(tree):
    kind = tree[0]
    if kind == "v":
        return frozenset((tree[1],))
    if kind == "0":
        return frozenset()
    if kind == "S":
        return free(tree[1])
    if kind == "I":
        return free(tree[1]) | free(tree[2]) | (free(tree[4]) - {tree[3]})
    if kind == "=":
        return free(tree[1]) | free(tree[2])
    return free(tree[3]) - set(tree[1:3])


def evaluate(term, environment):
    return _evaluate(term, tuple(sorted((x, environment[x]) for x in free(term))))


@lru_cache(None)
def _evaluate(term, assignment):
    environment = dict(assignment)
    kind = term[0]
    if kind == "v":
        return environment[term[1]]
    if kind == "0":
        return 0
    if kind == "S":
        return evaluate(term[1], environment) + 1
    _, n, a, bound, h = term
    counter, state = evaluate(n, environment), evaluate(a, environment)
    for _ in range(counter):
        environment[bound] = state
        state = evaluate(h, environment)
    return state


def matrix_for_prefix(length):
    # Every quantified variable occurs once; no vacuous-prefix example.
    term = ZERO
    for j in reversed(range(length)):
        term = iterator(var("x" + str(j)), term, suc)
    return eq(term, suc(ZERO))


def expand_prefix(length, universal):
    formula = matrix_for_prefix(length)
    for j in reversed(range(length)):
        formula = universal("x" + str(j), formula)
    return formula


def main():
    p = predecessor(var("n"))
    # Independent numerical checks of the fully expanded predecessor.
    predecessor_values = [evaluate(p, {"n": n}) for n in range(5)]
    if predecessor_values != [0, 0, 1, 2, 3]:
        raise ValueError(predecessor_values)
    rows = []
    for n in range(1, 11):
        old, new = expand_prefix(n, universal_old), expand_prefix(n, universal_new)
        if rank(old) != 2 * n or rank(new) != n:
            raise ValueError("rank mismatch")
        # Fully expanded P(n) contains exactly two free occurrences of n.
        expected_new = size(matrix_for_prefix(n)) + (size(p) - 1) * n + 7 * n
        if size(new) != expected_new or free(new) or free(old):
            raise ValueError("size/scope mismatch")
        if size(old) != (4 * n + 39) * 2 ** n + 2 * n - 35:
            raise ValueError("old closed form mismatch")
        if size(new) != 85 * n + 4:
            raise ValueError("new closed form mismatch")
        rows.append({"universals": n, "old_D_rank": rank(old),
                     "new_D_rank": rank(new), "old_tree_nodes": size(old),
                     "new_tree_nodes": size(new),
                     "old_terminal_payload": payload(old),
                     "new_terminal_payload": payload(new)})
    result = {"status": "finite checks passed; not a proof-assistant verification",
              "predecessor_nodes": size(p),
              "predecessor_values_0_through_4": predecessor_values,
              "comparison": rows,
              "scope": "Raw expanded native trees; no DAG sharing or term normalization."}
    target = Path(__file__).resolve().parents[1] / "evidence" / "macro_metrics.json"
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
