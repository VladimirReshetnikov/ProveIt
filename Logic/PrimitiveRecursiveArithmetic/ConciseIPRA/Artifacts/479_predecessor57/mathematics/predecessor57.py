"""Expanded scalar terms and finite checks for the 57-node predecessor.

This is an untrusted research utility, not an iPRA proof checker.  Arithmetic
definitions marked 'old' reproduce the pinned ConciseIPRA scalar bootstrap;
the new three-cycle and ramp are the contribution checked here.  All measured
terms expand to variables, zero, successor and a scalar iterator.  No DAG
sharing, normalization, implicit arithmetic symbols or binder-name cost is
included in the constructor-node metric.
"""
from functools import lru_cache
from itertools import count
import json
from pathlib import Path


serial = count()
ZERO = ("0",)


def fresh():
    return "b" + str(next(serial))


def var(name):
    return ("v", name)


def suc(term):
    return ("S", term)


def iterator(counter, seed, body):
    bound = fresh()
    return ("I", counter, seed, bound, body(var(bound)))


def select(control, first, second):
    return iterator(control, first, lambda _: second)


def add(first, second):
    return iterator(second, first, suc)


def zero_test(term):
    return select(term, suc(ZERO), ZERO)


def parity(term):
    return iterator(term, ZERO, zero_test)


def cycle_old(term):
    return iterator(term, ZERO,
                    lambda u: add(zero_test(u), add(parity(u), parity(u))))


def ramp_old(term):
    return iterator(term, ZERO, lambda u: suc(add(u, cycle_old(u))))


def cycle_step(term):
    return iterator(term, suc(suc(ZERO)), zero_test)


def cycle_new(term):
    return iterator(term, ZERO, cycle_step)


def ramp_new(term):
    return iterator(term, ZERO,
                    lambda u: suc(select(cycle_new(u), suc(u), u)))


def factor(term, ramp):
    return select(parity(term), ramp(term), term)


def power2(term):
    return iterator(term, suc(ZERO), lambda u: add(u, u))


def positive_power2(term):
    return suc(iterator(term, ZERO, lambda u: suc(add(u, u))))


def compare(first, second, ramp):
    return parity(iterator(second, power2(first), lambda u: factor(u, ramp)))


def predecessor(term, ramp):
    return iterator(term, ZERO, lambda u:
                    select(compare(suc(suc(u)), term, ramp), u, suc(u)))


def predecessor57(term):
    return iterator(term, ZERO, lambda u:
                    select(compare(term, suc(u), ramp_new), suc(u), u))


def size(term):
    if term[0] in ("0", "v"):
        return 1
    if term[0] == "S":
        return 1 + size(term[1])
    return 1 + size(term[1]) + size(term[2]) + size(term[4])


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
    tag = term[0]
    if tag == "0":
        return 0
    if tag == "v":
        return environment[term[1]]
    if tag == "S":
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
    n = var("n")
    terms = {
        "old_cycle": cycle_old(n),
        "new_cycle_step": cycle_step(n),
        "new_cycle": cycle_new(n),
        "old_ramp": ramp_old(n),
        "new_ramp": ramp_new(n),
        "old_factor": factor(n, ramp_old),
        "new_factor": factor(n, ramp_new),
        "old_predecessor": predecessor(n, ramp_old),
        "new_predecessor": predecessor(n, ramp_new),
        "predecessor57": predecessor57(n),
        "positive_power2": positive_power2(n),
    }
    expected = dict(old_cycle=30, new_cycle_step=10, new_cycle=13,
                    old_ramp=38, new_ramp=21, old_factor=48, new_factor=31,
                    old_predecessor=75, new_predecessor=58,
                    predecessor57=57,
                    positive_power2=10)
    sizes = {name: size(term) for name, term in terms.items()}
    require(sizes == expected, (sizes, expected))
    values = {}
    expected_values = {
        "new_cycle_step": lambda k: 2 if k == 0 else (k + 1) % 2,
        "new_cycle": lambda k: (0, 2, 1)[k % 3],
        "new_ramp": lambda k: (3 * k + 1) // 2,
        "new_factor": lambda k: k if k % 2 else 3 * k // 2,
    }
    for name, function in expected_values.items():
        actual = [evaluate(terms[name], {"n": k}) for k in range(25)]
        require(actual == [function(k) for k in range(25)], name)
        values[name] = actual
    # Expensive evaluations use the actual expanded scalar term, not a Python
    # predecessor builtin or a replacement numerical interpretation of R.
    p_values = [evaluate(terms["new_predecessor"], {"n": k}) for k in range(5)]
    require(p_values == [0, 0, 1, 2, 3], p_values)
    p57_values = [evaluate(terms["predecessor57"], {"n": k}) for k in range(5)]
    require(p57_values == [0, 0, 1, 2, 3], p57_values)

    # Separate, fast finite algebra checks of the claimed numerical identities.
    def r(k):
        return (3 * k + 1) // 2

    def h(k):
        return k if k % 2 else r(k)

    for k in range(1000):
        require((0, 2, 1)[r(k) % 3] == k % 2, ("invariant", k))
        require(r(k + 2) == r(k) + 3, ("two steps", k))
        require(r(2 * k) == 3 * k, ("doubling", k))
        require(r(3 * k) + k % 2 == 3 * r(k), ("tripling", k))
        require(h(2 * k) == 3 * k and h(3 * k) == 3 * h(k), ("factor", k))
    require(h(1) == 1, "factor fixed point")

    rows = [{"universal_prefix": k, "old_single_binder_nodes": 85 * k + 4,
             "new_single_binder_nodes": 67 * k + 4, "paired_binder_rank": k}
            for k in (1, 2, 4, 8, 16, 32)]
    result = {
        "status": "finite checks passed; not a proof-assistant verification",
        "metric": "fully expanded raw constructor nodes; no DAG sharing",
        "term_nodes": sizes,
        "literal_evaluator_values": values,
        "literal_predecessor_values_0_through_4": p_values,
        "literal_predecessor57_values_0_through_4": p57_values,
        "fast_algebra_checks": 5001,
        "universal_macro_family": rows,
        "universal_family_note": "These rows apply the proved size formula; the formula AST is independently constructed by block_macros.py.",
    }
    output = Path(__file__).with_name("predecessor57_results.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
