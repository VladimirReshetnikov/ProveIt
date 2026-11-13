"""Expanded scalar equality terms, counts, and finite diagnostics.

The proof is in equality_orbit.tex.  Finite tests here are not a proof.
All arithmetic macros expand into variables, zero, successor and one-state
iteration.  No DAG sharing is charged.  The evaluator executes the raw AST.
"""
from functools import lru_cache
from itertools import count
import json
from pathlib import Path

FRESH = count()
ZERO = ("zero",)


def var(name):
    return ("var", name)


def successor(t):
    return ("successor", t)


def iterate(counter, seed, body):
    name = "bound_" + str(next(FRESH))
    return ("iterate", counter, seed, name, body(var(name)))


def choose(c, a, b):
    return iterate(c, a, lambda _: b)


def zero_test(t):
    return choose(t, successor(ZERO), ZERO)


def parity(t):
    return iterate(t, ZERO, zero_test)


def complemented_parity(t):
    return iterate(t, successor(ZERO), zero_test)


def addition(a, b):
    return iterate(b, a, successor)


def exponential(a):
    return iterate(a, successor(ZERO), lambda u: addition(u, u))


def clock_step(v):
    return iterate(successor(v), v,
                   lambda w: choose(w, successor(v), ZERO))


def clock(n):
    return iterate(n, ZERO, clock_step)


def ramp(n):
    return iterate(n, ZERO, lambda u: successor(choose(clock(u), u, successor(u))))


def factor(n):
    return iterate(n, n, lambda v: choose(v, ramp(n), ZERO))


def orbit(counter, seed):
    return iterate(counter, seed, factor)


def delta(a, b):
    return parity(orbit(b, exponential(a)))


def eta(a, b):
    return complemented_parity(orbit(b, exponential(a)))


def predecessor45(n):
    return iterate(n, ZERO, lambda u:
                   choose(orbit(n, exponential(successor(u))), successor(u), u))


def predecessor52(n):
    return iterate(n, ZERO, lambda u:
                   choose(delta(successor(u), n), successor(u), u))


def subtraction(a, b):
    return iterate(b, a, predecessor45)


def previous_equality(a, b):
    r = subtraction(successor(a), b)
    return choose(r, successor(ZERO), predecessor45(r))


def size(t):
    tag = t[0]
    if tag in ("zero", "var"):
        return 1
    if tag == "successor":
        return 1 + size(t[1])
    if tag == "iterate":
        return 1 + size(t[1]) + size(t[2]) + size(t[4])
    raise ValueError(tag)


@lru_cache(None)
def free(t):
    tag = t[0]
    if tag == "zero":
        return frozenset()
    if tag == "var":
        return frozenset((t[1],))
    if tag == "successor":
        return free(t[1])
    return free(t[1]) | free(t[2]) | (free(t[4]) - {t[3]})


def occurrences(t, name):
    tag = t[0]
    if tag == "zero":
        return 0
    if tag == "var":
        return int(t[1] == name)
    if tag == "successor":
        return occurrences(t[1], name)
    return (occurrences(t[1], name) + occurrences(t[2], name)
            + (0 if t[3] == name else occurrences(t[4], name)))


def debruijn(t, scope=()):
    tag = t[0]
    if tag == "zero":
        return ("zero",)
    if tag == "var":
        return (("bound", scope.index(t[1])) if t[1] in scope
                else ("free", t[1]))
    if tag == "successor":
        return ("successor", debruijn(t[1], scope))
    return ("iterate", debruijn(t[1], scope), debruijn(t[2], scope),
            debruijn(t[4], (t[3],) + scope))


def check_bound_tree(t, depth=0):
    tag = t[0]
    if tag in ("zero", "free"):
        return 1
    if tag == "bound":
        require(type(t[1]) is int and 0 <= t[1] < depth, "bound index")
        return 1
    if tag == "successor":
        return 1 + check_bound_tree(t[1], depth)
    require(tag == "iterate" and len(t) == 4, "constructor")
    return (1 + check_bound_tree(t[1], depth) + check_bound_tree(t[2], depth)
            + check_bound_tree(t[3], depth + 1))


def evaluate(t, env):
    return eval_closed(t, tuple(sorted((x, env[x]) for x in free(t))))


@lru_cache(None)
def eval_closed(t, assignment):
    env = dict(assignment)
    tag = t[0]
    if tag == "zero":
        return 0
    if tag == "var":
        return env[t[1]]
    if tag == "successor":
        return 1 + evaluate(t[1], env)
    _, counter, seed, variable, body = t
    n, value = evaluate(counter, env), evaluate(seed, env)
    for _ in range(n):
        env[variable] = value
        value = evaluate(body, env)
    return value


def require(test, label):
    if not test:
        raise AssertionError(label)


def numerical_orbit(a, b):
    """Independent numeric description, not used by the raw AST evaluator."""
    value = 2 ** a
    for _ in range(b):
        value = 0 if value % 2 else 3 * value // 2
    return value


def main():
    a, b, n = var("a"), var("b"), var("n")
    terms = {
        "clock_step": clock_step(n), "clock": clock(n), "ramp": ramp(n),
        "factor": factor(n), "exponential": exponential(n),
        "orbit": orbit(b, exponential(a)), "delta": delta(a, b),
        "eta": eta(a, b), "predecessor45": predecessor45(n),
        "predecessor52": predecessor52(n),
        "previous_equality_using_predecessor45": previous_equality(a, b),
    }
    expected = {
        "clock_step": 9, "clock": 12, "ramp": 20, "factor": 26,
        "exponential": 9, "orbit": 37, "delta": 44, "eta": 45,
        "predecessor45": 45, "predecessor52": 52,
        "previous_equality_using_predecessor45": 193,
    }
    counts = {}
    for name, t in terms.items():
        counts[name] = size(t)
        require(counts[name] == expected[name], (name, counts[name]))
        require(check_bound_tree(debruijn(t)) == counts[name], name)
    multiplicities = {}
    for name in ("delta", "eta", "previous_equality_using_predecessor45"):
        require(free(terms[name]) == frozenset(("a", "b")), name)
        multiplicities[name] = {x: occurrences(terms[name], x) for x in ("a", "b")}
    require(multiplicities["delta"] == {"a": 1, "b": 1}, "delta multiplicity")
    require(multiplicities["eta"] == {"a": 1, "b": 1}, "eta multiplicity")
    require(multiplicities["previous_equality_using_predecessor45"] ==
            {"a": 3, "b": 3}, "old multiplicity")

    # Literal evaluation of the expanded raw trees on all 25 input pairs.
    literal = {}
    for name in ("delta", "eta"):
        table = []
        for x in range(5):
            row = []
            for y in range(5):
                value = evaluate(terms[name], {"a": x, "b": y})
                expected_value = int(x == y) if name == "delta" else int(x != y)
                require(value == expected_value, (name, x, y, value))
                row.append(value)
            table.append(row)
        literal[name] = table
    predecessor_values = {}
    for name in ("predecessor45", "predecessor52"):
        values = [evaluate(terms[name], {"n": x}) for x in range(6)]
        require(values == [0, 0, 1, 2, 3, 4], (name, values))
        predecessor_values[name] = values

    # Larger tests use only the separate numerical orbit description.
    for x in range(80):
        for y in range(80):
            value = numerical_orbit(x, y)
            require(value % 2 == int(x == y), ("numeric parity", x, y))
            if x and y:
                require(numerical_orbit(x, y) == 3 * numerical_orbit(x - 1, y - 1),
                        ("orbit recurrence", x, y))
    result = {
        "source_commit": "6c6a164d211f0af34e913d55c9f46f8ef7cb560f",
        "scope": "Derived scalar terms, not a new standalone proof checker.",
        "node_counts": counts, "free_input_occurrences": multiplicities,
        "literal_equality_tables_inputs_0_through_4": literal,
        "literal_predecessor_values_0_through_5": predecessor_values,
        "numeric_orbit_grid": [80, 80],
        "zero_true_equality_nodes_saved": 148,
        "zero_true_equality_percent_saved": 100 * 148 / 193,
        "limitations": ["Finite diagnostics are not formal proof-assistant verification.",
                        "Inherited floor-ramp and factor-map equations are explicit dependencies.",
                        "No minimum for equality terms or proof checkers is asserted."],
    }
    out = Path(__file__).resolve().parent
    (out / "equality_orbit_results.json").write_text(json.dumps(result, indent=2) + "\n")
    (out / "equality_orbit_asts.json").write_text(
        json.dumps({name: debruijn(terms[name]) for name in
                    ("delta", "eta", "predecessor52")}, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
