"""Finite transcription checks for the induction-free aperiodicity proof.

This is a numerical diagnostic, not a proof checker or a formal proof.
The all-elements theorem is established by the written finite derivations.
Run with Python 3; the only output is a JSON receipt on standard output.
"""

import json


def epsilon(x, y):
    return int(x == y)


def F(counter, update):
    state = update(0) + 1
    for _ in range(counter):
        state = update(state)
    return state


def D(counter, value):
    return F(counter, lambda state: value)


def increment(bit, value):
    return D(epsilon(bit, 0), value)


def cycle_term(k, value):
    result = 0
    for j in range(k):
        for _ in range(j + 1):
            result = increment(epsilon(value, j), result)
    return result


def iterate(update, count, value):
    for _ in range(count):
        value = update(value)
    return value


def main():
    tests = 0
    for value in range(12):
        assert increment(0, value) == value
        assert increment(1, value) == value + 1
        tests += 2
    cases = []
    for k in range(1, 17):
        update = lambda value, k=k: cycle_term(k, value)
        table = [update(value) for value in range(k + 1)]
        assert table == list(range(1, k + 1)) + [0]
        tests += 1
        for value in range(2 * k + 7):
            assert 0 <= update(value) <= k
            assert iterate(update, k, value) != value
            tests += 2
        for counter in range(12):
            assert F(counter + k, update) == iterate(
                update, k, F(counter, update)
            )
            tests += 1
        cases.append({"k": k, "cycle_table": table})
    print(json.dumps({
        "status": "passed",
        "assertions": tests,
        "fixed_cycle_lengths_checked": [1, 16],
        "source_theory_induction_used_in_written_proof": False,
        "source_theory_successor_injectivity_used_in_written_proof": False,
        "formal_verification": False,
        "purpose": "Finite transcription check; not a model-theoretic proof",
        "cases": cases,
    }, indent=2))


if __name__ == "__main__":
    main()
