"""Finite verification of the scalar support lemma.

This is an untrusted arithmetic experiment, not a proof checker for iPRA.
It expands every displayed helper into zero, successor, variables and
scalar iteration.  The six-state verification covers all states admitted
by the written range argument, including phases not reached at the small
numeral endpoints.  The universal range argument itself is in the report.
"""

import hashlib
import json
from pathlib import Path


def var(name):
    return ("var", name)


zero = ("zero",)


def succ(term):
    return ("succ", term)


def numeral(n):
    result = zero
    for _ in range(n):
        result = succ(result)
    return result


def iterate(counter, seed, variable, body):
    return ("iter", counter, seed, variable, body)


def choose(n, a, b):
    return iterate(n, a, "unused", b)


def zero_flag(n):
    return choose(n, numeral(1), zero)


def parity(n):
    return iterate(n, zero, "parity_state", zero_flag(var("parity_state")))


def ternary_step(u):
    return choose(u, numeral(1), choose(parity(u), zero, numeral(2)))


def ternary(n):
    return iterate(n, zero, "ternary_state", ternary_step(var("ternary_state")))


def theta0(v):
    return zero_flag(v)


def theta1(v):
    return parity(v)


def theta2(v):
    return choose(v, zero, zero_flag(parity(v)))


def phase_masks(p, q):
    return (
        choose(p, theta2(q), zero),
        choose(p, zero, theta0(q)),
        choose(p, theta1(q), zero),
    )


def supports(n):
    return phase_masks(parity(n), ternary(n))


def cycle(period, n):
    if period == 1:
        return zero
    name = f"phase_state_{period}"
    u = var(name)
    previous = cycle(period - 1, u)
    body = choose(u, numeral(1), choose(previous, zero, succ(previous)))
    return iterate(n, zero, name, body)


def shift(n, count):
    for _ in range(count):
        n = succ(n)
    return n


def general_support(period, target, n):
    return zero_flag(cycle(period, shift(n, period - target)))


def evaluate(term, environment=None):
    environment = {} if environment is None else environment
    tag = term[0]
    if tag == "zero":
        return 0
    if tag == "var":
        return environment[term[1]]
    if tag == "succ":
        return evaluate(term[1], environment) + 1
    if tag == "iter":
        _, counter, seed, name, body = term
        n = evaluate(counter, environment)
        value = evaluate(seed, environment)
        for _ in range(n):
            value = evaluate(body, dict(environment, **{name: value}))
        return value
    raise ValueError(f"Forbidden constructor: {tag}")


def inspect(term, bound=frozenset()):
    tag = term[0]
    if tag == "zero":
        assert len(term) == 1
        return 1, set()
    if tag == "var":
        assert len(term) == 2 and isinstance(term[1], str)
        return 1, set() if term[1] in bound else {term[1]}
    if tag == "succ":
        assert len(term) == 2
        size, free = inspect(term[1], bound)
        return 1 + size, free
    assert tag == "iter" and len(term) == 5
    _, counter, seed, name, body = term
    nc, fc = inspect(counter, bound)
    ns, fs = inspect(seed, bound)
    nb, fb = inspect(body, bound | {name})
    return 1 + nc + ns + nb, fc | fs | fb


def main():
    definitions = {
        "p": parity(var("n")),
        "T": ternary_step(var("u")),
        "q": ternary(var("n")),
        **{f"b{j}": term for j, term in zip((2, 3, 4), supports(var("n")))},
    }
    formation = {}
    for name, term in definitions.items():
        size, free = inspect(term)
        assert free == ({"u"} if name == "T" else {"n"})
        formation[name] = {"expanded_nodes": size, "free_variables": sorted(free)}

    p_transition = [evaluate(zero_flag(numeral(p))) for p in (0, 1)]
    q_transition = [evaluate(ternary_step(numeral(q))) for q in (0, 1, 2)]
    assert p_transition == [1, 0]
    assert q_transition == [1, 2, 0]
    theta_table = [
        [evaluate(fn(numeral(v))) for fn in (theta0, theta1, theta2)]
        for v in (0, 1, 2)
    ]
    assert theta_table == [[1, 0, 0], [0, 1, 0], [0, 0, 1]]

    states = [(p, q) for p in (0, 1) for q in (0, 1, 2)]
    masks = {}
    transitions = []
    for p, q in states:
        outputs = [evaluate(term) for term in phase_masks(numeral(p), numeral(q))]
        assert all(value in (0, 1) for value in outputs)
        assert sum(outputs) <= 1
        next_state = (p_transition[p], q_transition[q])
        next_outputs = [
            evaluate(term)
            for term in phase_masks(numeral(next_state[0]), numeral(next_state[1]))
        ]
        assert all(not value or next_outputs[j] == 0 for j, value in enumerate(outputs))
        masks[p, q] = outputs
        transitions.append({
            "state": [p, q], "masks": outputs,
            "successor": list(next_state), "successor_masks": next_outputs,
        })

    avoidance_pairs = 0
    for left in states:
        for right in states:
            assert any(not a and not b for a, b in zip(masks[left], masks[right]))
            avoidance_pairs += 1

    endpoints = {}
    for n in range(5):
        endpoints[n] = [evaluate(term) for term in supports(numeral(n))]
    assert endpoints[0] == endpoints[1] == [0, 0, 0]
    for index, target in enumerate((2, 3, 4)):
        assert endpoints[target][index] == 1

    general_periods = []
    for period in range(2, 6):
        term = cycle(period, var("n"))
        size, free = inspect(term)
        assert free == {"n"}
        finite_values = [evaluate(cycle(period, numeral(n))) for n in range(2 * period)]
        assert finite_values == [n % period for n in range(2 * period)]
        state_supports = []
        for state in range(period):
            masks_now = [
                evaluate(general_support(period, j, numeral(state)))
                for j in range(2, period)
            ]
            masks_next = [
                evaluate(general_support(period, j, numeral(state + 1)))
                for j in range(2, period)
            ]
            assert all(v in (0, 1) for v in masks_now)
            assert sum(masks_now) <= 1
            assert all(not v or masks_next[j] == 0 for j, v in enumerate(masks_now))
            if state < 2:
                assert not any(masks_now)
            else:
                assert masks_now[state - 2] == 1
            state_supports.append({"state": state, "masks": masks_now,
                                   "successor_masks": masks_next})
        general_periods.append({"period": period, "expanded_cycle_nodes": size,
                                "fixed_numeral_values": finite_values,
                                "support_phase_cases": state_supports})

    receipt = {
        "status": "PASS",
        "scope": "Expanded scalar term formation and exhaustive finite phase checks; no universal proof-assistant claim",
        "constructors": ["zero", "succ", "var", "iter"],
        "uses_predecessor": False,
        "uses_comparator": False,
        "formation": formation,
        "parity_transition": p_transition,
        "ternary_transition": q_transition,
        "theta_table": theta_table,
        "phase_cases": transitions,
        "avoidance_state_pairs": avoidance_pairs,
        "numeral_endpoints": endpoints,
        "general_period_compiler": general_periods,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    destination = Path(__file__).resolve().parent.parent / "evidence" / "scalar_supports_validation.json"
    destination.write_text(json.dumps(receipt, indent=2) + "\n")
    terms_path = Path(__file__).resolve().parent.parent / "fixtures" / "scalar_support_terms.json"
    terms_path.write_text(json.dumps(definitions, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "phase_cases": len(states),
                      "avoidance_pairs": avoidance_pairs,
                      "receipt": str(destination), "terms": str(terms_path)}))


if __name__ == "__main__":
    main()
