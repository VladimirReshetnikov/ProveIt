"""Independent finite example for protected-level coordinate rebasing.

Numerical root depth is 3. The initial protected levels 0, 1, 2
denote zero. Successor adds four dummy zero slots. Iterator adds
two slots to every child: both zero in counter/initializer, and
both aliases of the current state in the update. The displayed
canonical updates use the first of these two state slots.
Only the displayed finite evaluations are claimed by this script.
"""
import json


def value(term, environment=(0, 0, 0)):
    if type(term) is int:
        if not 0 <= term < len(environment):
            raise ValueError("unbound protected level")
        return environment[term]
    if type(term) is not list:
        raise ValueError("expected an integer or a list")
    if len(term) == 1:
        return 1 + value(term[0], environment + (0, 0, 0, 0))
    if len(term) == 3:
        count, seed, update = term
        passive = environment + (0, 0)
        iterations = value(count, passive)
        state = value(seed, passive)
        for _ in range(iterations):
            state = value(update, environment + (state, state))
        return state
    raise ValueError("outside the displayed canonical numerical grammar")


def main():
    examples = {
        "original_outer_zero_iterator": [0, [[0], [0], [5]], 0],
        "naively_erased_initializer": [[0], [0], [5]],
        "correctly_rebased_initializer": [[0], [0], [3]],
    }
    results = {name: value(term) for name, term in examples.items()}
    expected = {
        "original_outer_zero_iterator": 2,
        "naively_erased_initializer": 1,
        "correctly_rebased_initializer": 2,
    }
    if results != expected:
        raise AssertionError((results, expected))
    print(json.dumps({"status": "PASS", "values": results,
                      "scope": "finite example, not universal verification"},
                     indent=2))


if __name__ == "__main__":
    main()
