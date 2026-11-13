"""Fully expanded scalar terms for an absorbing-orbit predecessor.

This is an untrusted arithmetic experiment, not a proof checker.  The
57-node control and its clock/ramp are reproduced from ProveIt incoming
ipra_479_predecessor57_2026-11-12 at commit e85c5e24dba535a296c46cd18fa66a146ce36b8e
(MIT-0).  The absorbing factor and 51-node term are the present change.
Every abbreviation expands into variables, zero, successor and scalar
iteration; sizes count constructor occurrences, without DAG sharing.
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
    bound = "b" + str(next(serial))
    return ("I", counter, seed, bound, body(var(bound)))


def select(control, first, second):
    return iterator(control, first, lambda _: second)


def add(first, second):
    return iterator(second, first, suc)


def zero_test(term):
    return select(term, suc(ZERO), ZERO)


def parity(term):
    return iterator(term, ZERO, zero_test)


def cycle_step(term):
    return iterator(term, suc(suc(ZERO)), zero_test)


def clock(term):
    return iterator(term, ZERO, cycle_step)


def ramp(term):
    return iterator(term, ZERO,
                    lambda u: suc(select(clock(u), suc(u), u)))


def factor_control(term):
    return select(parity(term), ramp(term), term)


def factor_absorbing(term):
    return select(parity(term), ramp(term), ZERO)


def power2(term):
    return iterator(term, suc(ZERO), lambda u: add(u, u))


def compare_control(first, second):
    return parity(iterator(second, power2(first), factor_control))


def predecessor57(term):
    return iterator(term, ZERO, lambda u:
                    select(compare_control(term, suc(u)), suc(u), u))


def predecessor51(term):
    return iterator(term, ZERO, lambda u:
                    select(iterator(suc(suc(u)), power2(term),
                                    factor_absorbing), u, suc(u)))


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
    terms = {"clock": clock(n), "ramp": ramp(n),
             "power2": power2(n),
             "factor_control": factor_control(n),
             "factor_absorbing": factor_absorbing(n),
             "predecessor57": predecessor57(n),
             "predecessor51": predecessor51(n)}
    sizes = {name: size(term) for name, term in terms.items()}
    expected = {"clock": 13, "ramp": 21, "power2": 9,
                "factor_control": 31, "factor_absorbing": 31,
                "predecessor57": 57, "predecessor51": 51}
    require(sizes == expected, (sizes, expected))

    # The slow evaluator receives the literal expanded AST, not a numerical
    # implementation of R, H, comparison, or predecessor.
    literal_values = [evaluate(terms["predecessor51"], {"n": k}) for k in range(5)]
    require(literal_values == [0, 0, 1, 2, 3], literal_values)
    factor_values = [evaluate(terms["factor_absorbing"], {"n": k}) for k in range(25)]
    require(factor_values == [0 if k % 2 else 3 * k // 2 for k in range(25)],
            "absorbing factor literal values")

    # Separate fast numerical checks; these are not the internal proof.
    def h(k):
        return 0 if k % 2 else 3 * k // 2

    def orbit(counter, seed):
        value = seed
        for _ in range(counter):
            value = h(value)
        return value

    def lam(x, y):
        return int(orbit(y + 1, 2 ** x) == 0)

    def pred_fast(m):
        value = 0
        for _ in range(m):
            witness = orbit(value + 2, 2 ** m)
            value = value if witness == 0 else value + 1
        return value

    for k in range(1000):
        require(h(2 * k) == 3 * k, ("doubling", k))
        require(h(3 * k) == 3 * h(k), ("tripling", k))
    require(h(0) == 0 and h(1) == 0, "absorbing values")
    for x in range(33):
        require(lam(x + 1, 0) == 0, ("comparator right base", x))
        for y in range(33):
            require(lam(0, y) == 1, ("comparator left base", y))
            require(lam(x + 1, y + 1) == lam(x, y), ("comparator step", x, y))
            require(lam(x, y) == int(x <= y), ("numerical reading", x, y))
    fast_values = [pred_fast(k) for k in range(65)]
    require(fast_values == [max(k - 1, 0) for k in range(65)], "fast predecessor")

    result = {
        "status": "finite checks passed; general validity is a written equational proof",
        "metric": "fully expanded raw constructor occurrences, no sharing or normalization",
        "term_nodes": sizes,
        "literal_predecessor_values_0_through_4": literal_values,
        "literal_factor_values_0_through_24": factor_values,
        "fast_predecessor_values_0_through_64": fast_values,
        "factor_checks": 2001,
        "comparator_grid": [33, 33],
        "compiler_family_nodes": [{"quantifiers": k, "predecessor57": 67 * k + 4,
                                    "predecessor51": 61 * k + 4}
                                   for k in (1, 2, 4, 8, 16, 32)],
        "scope": "This reduces a derived arithmetic term, not the standalone proof-checker size."
    }
    Path(__file__).with_name("predecessor51_results.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
