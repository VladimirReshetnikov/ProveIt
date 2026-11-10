"""Numerical transcription checks for the no-injectivity right predecessor.

This does not test independence of successor injectivity or replace the
written arbitrary-element proof. It evaluates the terms on ordinary naturals.
"""

import json


def F(counter, update):
    value = update(0) + 1
    for _ in range(counter):
        value = update(value)
    return value


def h(target, value):
    return value if value == 0 or value + 1 == target else value + 1


def V(counter, target):
    return F(counter, lambda value: h(target, value))


def W(target):
    return V(target, target)


def P(value):
    return 0 if value in (0, 1) else W(value)


def main():
    assertions = 0
    for target in range(50):
        for counter in range(50):
            value = V(counter, target)
            assert value == counter + 1 or value + 1 == target
            assertions += 1
    for value in range(100):
        assert W(value + 2) + 1 == value + 2
        assert value == 0 or value == P(value) + 1
        assert P(value + 1) + 1 == value + 1
        assertions += 3
    print(json.dumps({
        "status": "passed",
        "assertions": assertions,
        "formal_verification": False,
        "purpose": (
            "Standard numerical transcription check of capped-clock and "
            "right-predecessor formulas; not a proof of injectivity independence"
        ),
    }, indent=2))


if __name__ == "__main__":
    main()
