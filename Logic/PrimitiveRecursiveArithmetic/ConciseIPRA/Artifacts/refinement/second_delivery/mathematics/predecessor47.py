"""Expanded scalar predecessor terms, exact sizes, and finite checks.

This is an untrusted research utility, not a proof checker for iPRA.
The universal theorem is proved equationally in predecessor47.tex.

The 57-node control and its clock/ramp definitions are transcribed from
ProveIt's incoming ipra_479_predecessor57_2026-11-12.zip. The current
50-node weighted control is from ipra_absorbing_predecessor_2026-11-12.zip
at final inspected commit 2c7617bb03bbbb15a4534c5468f7df8da22c7ab4.
That newer package already supplies the absorbing orbit, selector
cancellation, and general amplitude-toggle lemma. The new contributions
are applying the toggle directly to the ramp payload (28-node factor),
reversing the comparison orientation, and their 47-node combination.

The AST evaluator knows only variables, zero, successor and iteration.
Its two generic optimizations are iteration of a constant function and
skipping a cycle after the same numerical state has actually recurred.
Neither recognizes an arithmetic macro or substitutes a closed-form ramp,
factor, comparator, or predecessor.
"""

from functools import lru_cache
from itertools import count
import json
from pathlib import Path
import platform


SERIAL = count()
ZERO = ("0",)


def variable(name):
    return ("v", name)


def successor(term):
    return ("S", term)


def iterator(counter, seed, body):
    binder = "b" + str(next(SERIAL))
    return ("I", counter, seed, binder, body(variable(binder)))


def selector(control, first, second):
    return iterator(control, first, lambda unused: second)


def addition(first, second):
    return iterator(second, first, successor)


def zero_test(term):
    return selector(term, successor(ZERO), ZERO)


def parity(term):
    return iterator(term, ZERO, zero_test)


def clock_step(term):
    return iterator(term, successor(successor(ZERO)), zero_test)


def clock(term):
    return iterator(term, ZERO, clock_step)


def ramp(term):
    return iterator(term, ZERO, lambda state:
                    successor(selector(clock(state), successor(state), state)))


def power2(term):
    return iterator(term, successor(ZERO), lambda state: addition(state, state))


def retained_factor(term):
    return selector(parity(term), ramp(term), term)


def absorbing_factor(term):
    return selector(parity(term), ramp(term), ZERO)


def toggle_factor(term):
    return iterator(successor(term), ZERO,
                    lambda state: selector(state, ramp(term), ZERO))


def weighted_parity(term):
    return iterator(term, ZERO, lambda state: selector(state, term, ZERO))


def weighted_factor(term):
    return selector(weighted_parity(term), ramp(term), ZERO)


def old_compare(first, second):
    return parity(iterator(second, power2(first), retained_factor))


def strict_compare(first, second):
    return zero_test(iterator(second, power2(first), absorbing_factor))


def predecessor57(term):
    return iterator(term, ZERO, lambda state:
                    selector(old_compare(term, successor(state)),
                             successor(state), state))


def predecessor54(term):
    return iterator(term, ZERO, lambda state:
                    selector(strict_compare(successor(state), term),
                             state, successor(state)))


def predecessor50(term):
    return iterator(term, ZERO, lambda state:
                    selector(iterator(term, power2(successor(state)),
                                      absorbing_factor),
                             successor(state), state))


def predecessor47(term):
    return iterator(term, ZERO, lambda state:
                    selector(iterator(term, power2(successor(state)),
                                      toggle_factor),
                             successor(state), state))


def current_predecessor50(term):
    """Exact current-HEAD 50-node control, with a 30-node weighted factor."""
    return iterator(term, ZERO, lambda state:
                    selector(iterator(successor(successor(state)), power2(term),
                                      weighted_factor),
                             state, successor(state)))


def weighted_reversed49(term):
    return iterator(term, ZERO, lambda state:
                    selector(iterator(term, power2(successor(state)),
                                      weighted_factor),
                             successor(state), state))


def toggle_original48(term):
    return iterator(term, ZERO, lambda state:
                    selector(iterator(successor(successor(state)), power2(term),
                                      toggle_factor),
                             state, successor(state)))


def size(term):
    if term[0] in ("0", "v"):
        return 1
    if term[0] == "S":
        return 1 + size(term[1])
    return 1 + size(term[1]) + size(term[2]) + size(term[4])


def tag_inventory(term):
    counts = {"variable": 0, "zero": 0, "successor": 0, "iterator": 0}

    def visit(node):
        if node[0] == "0":
            counts["zero"] += 1
        elif node[0] == "v":
            counts["variable"] += 1
        elif node[0] == "S":
            counts["successor"] += 1
            visit(node[1])
        else:
            counts["iterator"] += 1
            visit(node[1])
            visit(node[2])
            visit(node[4])

    visit(term)
    return counts


@lru_cache(None)
def free_variables(term):
    if term[0] == "0":
        return frozenset()
    if term[0] == "v":
        return frozenset((term[1],))
    if term[0] == "S":
        return free_variables(term[1])
    return (free_variables(term[1]) | free_variables(term[2]) |
            (free_variables(term[4]) - {term[3]}))


def evaluate(term, environment):
    assignment = tuple(sorted((name, environment[name])
                              for name in free_variables(term)))
    return evaluate_closed(term, assignment)


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
    _, counter, seed, binder, body = term
    iterations = evaluate(counter, environment)
    if iterations < 0:
        raise ValueError("Scalar terms are evaluated over the natural numbers.")
    value = evaluate(seed, environment)
    if not iterations:
        return value
    if binder not in free_variables(body):
        return evaluate(body, environment)
    seen = {}
    index = 0
    while index < iterations:
        if value in seen:
            period = index - seen[value]
            remaining = (iterations - index) % period
            for _ in range(remaining):
                environment[binder] = value
                value = evaluate(body, environment)
            return value
        seen[value] = index
        environment[binder] = value
        value = evaluate(body, environment)
        index += 1
    return value


def render(term):
    tag = term[0]
    if tag == "0":
        return "0"
    if tag == "v":
        return term[1]
    if tag == "S":
        return "S(" + render(term[1]) + ")"
    return ("I(" + render(term[1]) + ", " + render(term[2]) + "; " +
            term[3] + "." + render(term[4]) + ")")


def require(condition, description):
    if not condition:
        raise AssertionError(description)


def fast_factor(value):
    return 0 if value % 2 else 3 * value // 2


def fast_orbit(count, seed):
    value = seed
    for _ in range(count):
        value = fast_factor(value)
        if value == 0:
            return 0
    return value


def fast_comparator(first, second):
    return int(fast_orbit(second, 1 << first) == 0)


def fast_predecessor(value):
    state = 0
    for _ in range(value):
        signal = fast_orbit(value, 1 << (state + 1))
        state = state + 1 if signal == 0 else state
    return state


def main():
    output = Path(__file__).resolve().parent
    n = variable("n")
    terms = {
        "clock_step": clock_step(n),
        "clock": clock(n),
        "ramp": ramp(n),
        "power2": power2(n),
        "retained_factor": retained_factor(n),
        "absorbing_factor": absorbing_factor(n),
        "weighted_parity": weighted_parity(n),
        "weighted_factor": weighted_factor(n),
        "toggle_factor": toggle_factor(n),
        "predecessor57": predecessor57(n),
        "predecessor54": predecessor54(n),
        "predecessor50": predecessor50(n),
        "current_predecessor50": current_predecessor50(n),
        "weighted_reversed49": weighted_reversed49(n),
        "toggle_original48": toggle_original48(n),
        "predecessor47": predecessor47(n),
    }
    expected = {
        "clock_step": 10, "clock": 13, "ramp": 21, "power2": 9,
        "retained_factor": 31, "absorbing_factor": 31, "weighted_parity": 7,
        "weighted_factor": 30, "toggle_factor": 28,
        "predecessor57": 57, "predecessor54": 54,
        "predecessor50": 50, "current_predecessor50": 50,
        "weighted_reversed49": 49, "toggle_original48": 48, "predecessor47": 47,
    }
    sizes = {name: size(term) for name, term in terms.items()}
    require(sizes == expected, (sizes, expected))

    primitive_values = {}
    for name, expected_function in [
        ("clock", lambda v: (0, 2, 1)[v % 3]),
        ("ramp", lambda v: (3 * v + 1) // 2),
        ("absorbing_factor", fast_factor),
        ("weighted_factor", fast_factor),
        ("toggle_factor", fast_factor),
    ]:
        actual = [evaluate(terms[name], {"n": value}) for value in range(65)]
        require(actual == [expected_function(value) for value in range(65)], name)
        primitive_values[name] = actual

    # These calls use the actual expanded AST and the four-constructor
    # interpreter above, not fast_predecessor or a recognized macro.
    literal_values = {}
    for name in ("predecessor57", "predecessor54", "predecessor50",
                 "current_predecessor50", "weighted_reversed49",
                 "toggle_original48", "predecessor47"):
        actual = [evaluate(terms[name], {"n": value}) for value in range(9)]
        require(actual == [max(value - 1, 0) for value in range(9)], name)
        literal_values[name] = actual

    algebra_checks = 0
    for value in range(1000):
        r = (3 * value + 1) // 2
        require((0, 2, 1)[r % 3] == value % 2, ("ramp invariant", value))
        require(fast_factor(2 * value) == 3 * value, ("factor doubling", value))
        require(fast_factor(3 * value) == 3 * fast_factor(value),
                ("factor tripling", value))
        algebra_checks += 3
    for first in range(40):
        require(fast_comparator(first, 0) == 0, ("comparator zero", first))
        require(fast_comparator(0, first + 1) == 1, ("comparator positive", first))
        algebra_checks += 2
        for second in range(40):
            require(fast_comparator(first + 1, second + 1) ==
                    fast_comparator(first, second), ("comparator shift", first, second))
            require(fast_comparator(first, second) == int(first < second),
                    ("comparator reading", first, second))
            algebra_checks += 2
    fast_values = [fast_predecessor(value) for value in range(129)]
    require(fast_values == [max(value - 1, 0) for value in range(129)],
            "fast numerical predecessor, values 0 through 128")

    artifact = {
        "constructors": {"0": "zero", "v": "variable", "S": "successor",
                         "I": "iterator (counter, seed, binder, body)"},
        "metric": "One node per variable, zero, S or I occurrence; no sharing.",
        "size": size(terms["predecessor47"]),
        "inventory": tag_inventory(terms["predecessor47"]),
        "term": terms["predecessor47"],
        "fully_expanded_text": render(terms["predecessor47"]),
    }
    (output / "predecessor47_ast.json").write_text(json.dumps(artifact, indent=2) + "\n")
    (output / "predecessor47_expanded.txt").write_text(
        artifact["fully_expanded_text"] + "\n\n" +
        "Raw constructor inventory: " + json.dumps(artifact["inventory"], sort_keys=True) + "\n" +
        "Total: 47. Binder names are annotations. No definitions or sharing remain.\n")
    report = {
        "python": platform.python_version(),
        "status": "All finite checks passed; general correctness is a written equational proof.",
        "proof_assistant_formalization": False,
        "term_nodes": sizes,
        "predecessor47_inventory": artifact["inventory"],
        "literal_ast_evaluator": {
            "range": [0, 8], "values": literal_values,
            "generic_optimizations": ["constant-function iteration", "observed finite-state cycles"],
            "macro_replacements": False,
        },
        "literal_factor_and_ramp_range": [0, 64],
        "literal_factor_and_ramp_values": primitive_values,
        "fast_numerical_checks": {
            "algebra_checks": algebra_checks,
            "predecessor_range": [0, 128],
            "predecessor_values": fast_values,
            "note": "Separate numerical model; this is not literal AST evaluation.",
        },
        "macro_size_formula": {"historical57": "67*n+4", "current50": "60*n+4",
                               "candidate47": "57*n+4",
                               "scope": "Single-binder universal macro; one occurrence per variable."},
    }
    (output / "predecessor47_results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("literal_factor_and_ramp_values", "fast_numerical_checks")}, indent=2))


if __name__ == "__main__":
    main()
