"""Check the six finite packet endpoint traces, not the equivalence theorem.

The payloads x, hx, t, r are opaque free variables. Reductions deliberately stop
at a payload, so no property of its internal numerical term is assumed.
"""
import json
from pathlib import Path


def successor(n):
    return ("S", n)


def iterator(n, seed, variable, body):
    return ("I", n, seed, variable, body)


def selector(n, zero, positive):
    return iterator(n, zero, "unused", positive)


def substitute(term, variable, value):
    # Bound names here are chosen fresh from all six fixed payload names.
    if not isinstance(term, tuple):
        return value if term == variable else term
    if term[0] == "S":
        return successor(substitute(term[1], variable, value))
    _, count, seed, binder, body = term
    return iterator(
        substitute(count, variable, value),
        substitute(seed, variable, value),
        binder,
        body if binder == variable else substitute(body, variable, value),
    )


def head_step(term):
    """One contraction and its counter-spine depth; no full normalization."""
    if not isinstance(term, tuple) or term[0] != "I":
        return None
    _, count, seed, binder, body = term
    if count == 0:
        return seed, 0
    if isinstance(count, tuple) and count[0] == "S":
        prior = iterator(count[1], seed, binder, body)
        return substitute(body, binder, prior), 0
    inner = head_step(count)
    if inner is None:
        return None
    return iterator(inner[0], seed, binder, body), inner[1] + 1


def numeral(n):
    value = 0
    for _ in range(n):
        value = successor(value)
    return value


def parity(n):
    return iterator(n, 0, "u", selector("u", successor(0), 0))


def endpoint(n, first, second):
    count = numeral(n)
    return selector(count, 0, selector(parity(count), first, second))


def check():
    expected_depths = [[0], [0, 1, 2, 1, 0], [0, 1, 2, 3, 2, 1, 0]]
    results = []
    for n in range(3):
        for first, second in [("x", "hx"), ("t", "r")]:
            term = endpoint(n, first, second)
            depths = []
            # A fixed bound suffices for these displayed traces; this loop does
            # not claim termination of arbitrary iterator evaluation.
            for _ in range(8):
                reduced = head_step(term)
                if reduced is None:
                    break
                term, depth = reduced
                depths.append(depth)
            expected = 0 if n == 0 else second if n == 1 else first
            assert term == expected
            assert depths == expected_depths[n]
            results.append({"row": n, "payloads": [first, second],
                            "counter_depths": depths, "endpoint": term})
    return results


if __name__ == "__main__":
    results = check()
    target = Path(__file__).with_name("bounded_conversion_trace.json")
    target.write_text(json.dumps(results, indent=2) + "\n")
    print("All six packet endpoint traces checked; maximum depth is 3.")
