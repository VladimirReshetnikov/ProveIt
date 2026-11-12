"""Expanded scalar predecessor terms and reproducible finite diagnostics.

The new contribution is P50: an absorbing factor map, a strict comparator,
and selector fusion.  J/M/R and P57 reproduce the incoming 57-node package.
This is an untrusted research utility, not a proof checker or a formal proof.
Only the constructors zero, variable, successor, and scalar iteration occur
in the measured trees.  Binder names are annotations; there is no sharing.
"""

from functools import lru_cache
from itertools import count
import json
from pathlib import Path

serial = count()
ZERO = ("0",)


def var(name):
    return ("v", name)


def suc(term):
    return ("S", term)


def iterator(counter, seed, body):
    name = "b" + str(next(serial))
    return ("I", counter, seed, name, body(var(name)))


def select(control, first, second):
    return iterator(control, first, lambda _: second)


def add(first, second):
    return iterator(second, first, suc)


def zero_test(term):
    return select(term, suc(ZERO), ZERO)


def parity(term):
    return iterator(term, ZERO, zero_test)


def clock_step(term):
    return iterator(term, suc(suc(ZERO)), zero_test)


def clock(term):
    return iterator(term, ZERO, clock_step)


def ramp(term):
    return iterator(term, ZERO,
                    lambda u: suc(select(clock(u), suc(u), u)))


def factor_fixed(term):
    return select(parity(term), ramp(term), term)


def factor_absorbing(term):
    return select(parity(term), ramp(term), ZERO)


def power2(term):
    return iterator(term, suc(ZERO), lambda u: add(u, u))


def orbit(first, second):
    return iterator(second, power2(first), factor_absorbing)


def strict_compare(first, second):
    return zero_test(orbit(first, second))


def predecessor54(term):
    return iterator(term, ZERO, lambda u:
                    select(strict_compare(suc(u), term), u, suc(u)))


def predecessor50(term):
    return iterator(term, ZERO, lambda u:
                    select(orbit(suc(u), term), suc(u), u))


def predecessor57(term):
    def le(first, second):
        return parity(iterator(second, power2(first), factor_fixed))
    return iterator(term, ZERO,
                    lambda u: select(le(term, suc(u)), suc(u), u))


def size(term):
    if term[0] in ("0", "v"):
        return 1
    if term[0] == "S":
        return 1 + size(term[1])
    return 1 + size(term[1]) + size(term[2]) + size(term[4])


def debruijn(term, binders=()):
    """A binding-explicit tree with no names on bound variable occurrences."""
    if term[0] == "0":
        return ("0",)
    if term[0] == "v":
        name = term[1]
        return ("b", binders.index(name)) if name in binders else ("f", name)
    if term[0] == "S":
        return ("S", debruijn(term[1], binders))
    return ("I", debruijn(term[1], binders), debruijn(term[2], binders),
            debruijn(term[4], (term[3],) + binders))


def check_debruijn(term, depth=0):
    """Independently count the new tree and reject any escaping bound index."""
    if term[0] == "0":
        return 1
    if term[0] == "b":
        require(type(term[1]) is int and 0 <= term[1] < depth, "bound index")
        return 1
    if term[0] == "f":
        require(term[1] == "n", "free parameter")
        return 1
    if term[0] == "S":
        return 1 + check_debruijn(term[1], depth)
    require(term[0] == "I" and len(term) == 4, "iterator grammar")
    return (1 + check_debruijn(term[1], depth)
            + check_debruijn(term[2], depth)
            + check_debruijn(term[3], depth + 1))


@lru_cache(None)
def free(term):
    if term[0] == "0":
        return frozenset()
    if term[0] == "v":
        return frozenset((term[1],))
    if term[0] == "S":
        return free(term[1])
    return free(term[1]) | free(term[2]) | (free(term[4]) - {term[3]})


def evaluate(term, environment):
    return evaluate_closed(term, tuple(sorted((v, environment[v]) for v in free(term))))


@lru_cache(None)
def evaluate_closed(term, assignment):
    environment = dict(assignment)
    if term[0] == "0":
        return 0
    if term[0] == "v":
        return environment[term[1]]
    if term[0] == "S":
        return evaluate(term[1], environment) + 1
    _, counter, seed, bound, body = term
    iterations = evaluate(counter, environment)
    value = evaluate(seed, environment)
    for _ in range(iterations):
        environment[bound] = value
        value = evaluate(body, environment)
    return value


def require(condition, description):
    if not condition:
        raise ValueError(description)


def main():
    n, x, y = var("n"), var("x"), var("y")
    terms = {
        "zero_test": zero_test(n), "parity": parity(n),
        "clock_step": clock_step(n), "clock": clock(n), "ramp": ramp(n),
        "factor_absorbing": factor_absorbing(n), "power2": power2(n),
        "strict_compare": strict_compare(x, y),
        "predecessor54": predecessor54(n),
        "predecessor50": predecessor50(n),
        "predecessor57": predecessor57(n),
    }
    expected_sizes = {
        "zero_test": 5, "parity": 8, "clock_step": 10, "clock": 13,
        "ramp": 21, "factor_absorbing": 31, "power2": 9,
        "strict_compare": 46, "predecessor54": 54,
        "predecessor50": 50, "predecessor57": 57,
    }
    sizes = {name: size(term) for name, term in terms.items()}
    require(sizes == expected_sizes, (sizes, expected_sizes))
    require(free(terms["predecessor50"]) == frozenset(("n",)), "free variables")
    db_tree = debruijn(terms["predecessor50"])
    require(check_debruijn(db_tree) == 50, "independent de Bruijn node count")

    literal = {}
    expected_predecessors = [0, 0, 1, 2, 3, 4, 5]
    for name in ("predecessor50", "predecessor54", "predecessor57"):
        literal[name] = [evaluate(terms[name], {"n": k}) for k in range(7)]
        require(literal[name] == expected_predecessors, (name, literal[name]))
    factor_values = [evaluate(terms["factor_absorbing"], {"n": k}) for k in range(25)]
    require(factor_values == [0 if k % 2 else 3 * k // 2 for k in range(25)], "factor values")

    comparator_values = []
    for first in range(5):
        row = []
        for second in range(7):
            value = evaluate(terms["strict_compare"], {"x": first, "y": second})
            require(value == int(first < second), ("literal comparator", first, second, value))
            row.append(value)
        comparator_values.append(row)

    # These faster diagnostics use numerical definitions.  They are separate
    # from the literal syntax evaluator and are not universal proofs.
    def h(a):
        return 0 if a % 2 else 3 * a // 2

    def o(a, b):
        value = 2 ** a
        for _ in range(b):
            value = h(value)
        return value

    def k(a, b):
        return int(o(a, b) == 0)

    def w(t, m):
        value = 0
        for _ in range(t):
            if k(value, m):
                value += 1
        return value

    fast_checks = 0
    for a in range(500):
        require(h(2 * a) == 3 * a, ("factor doubling", a))
        require(h(3 * a) == 3 * h(a), ("factor scaling", a))
        fast_checks += 2
    for a in range(20):
        require(k(a, 0) == 0 and k(0, a + 1) == 1 and k(a, a) == 0,
                ("comparator endpoints", a))
        require(w(a, a) == a and w(a + 1, a) == a, ("saturation", a))
        fast_checks += 2
        for b in range(20):
            require(k(a + 1, b + 1) == k(a, b), ("comparator recurrence", a, b))
            require(w(a + 1, b + 1) == w(a, b) + 1, ("shift", a, b))
            fast_checks += 2

    result = {
        "status": "finite diagnostics passed; no proof-assistant formalization",
        "metric": "fully expanded raw constructor nodes; no sharing or normalization",
        "term_nodes": sizes,
        "debruijn_node_count": check_debruijn(db_tree),
        "debruijn_scope_check": "passed: all bound indices in scope, only n free",
        "literal_predecessor_values_0_through_6": literal,
        "literal_factor_values_0_through_24": factor_values,
        "literal_strict_comparator_rows_x0_through_4_columns_y0_through_6": comparator_values,
        "fast_identity_checks": fast_checks,
        "improvement_over_incoming57": {"nodes_saved": 7, "fraction": "7/57"},
        "scope": "Arithmetic term reduction only; unchanged primitive proof calculus.",
        "provenance": "Clock/ramp and predecessor57 from ipra_479_predecessor57_2026-11-12; absorbing factor, strict comparator, and predecessor50 are this extension.",
    }
    destination = Path(__file__).resolve().parents[2] / "evidence"
    destination.mkdir(exist_ok=True)
    (destination / "pred50_results.json").write_text(json.dumps(result, indent=2) + "\n")
    (destination / "pred50_expanded_ast.json").write_text(
        json.dumps(terms["predecessor50"], indent=2) + "\n")
    (destination / "pred50_debruijn_ast.json").write_text(
        json.dumps(db_tree, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
