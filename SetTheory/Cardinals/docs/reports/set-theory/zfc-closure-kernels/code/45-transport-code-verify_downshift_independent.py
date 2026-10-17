#!/usr/bin/env python3
"""Independent literal checks for the optimized G/V finite downshift.

G acts as [1,0,0] on names [0,1,2], and fixes all other integers.
U(x)=x+1 and V(x)=G(x)-1. Execution order is left to right.
The universal proof is elementary; finite checks are supporting evidence.
No Turing-machine state count or consistency statement is asserted here.
"""

from itertools import combinations
import json


def v(x: int) -> int:
    if x == 0:
        return 0
    if x == 1 or x == 2:
        return -1
    return x - 1


def macro(support: set[int]) -> tuple[int, int, int]:
    if not support:
        return 0, 0, 0
    a = max(0, 2 - min(support))
    c = max(0, max(support))
    b = a - 1 + c
    assert b >= 1
    return a, b, c


def literal_run(exponents: tuple[int, int, int], x: int) -> int:
    a, b, c = exponents
    for _ in range(a):
        x += 1
    for _ in range(b):
        x = v(x)
    for _ in range(c):
        x += 1
    return x


def verify() -> dict:
    counts = {"exact_G": 0, "orbit_cases": 0,
              "finite_supports": 0, "live_values": 0}
    for x in range(-1000, 1001):
        expected = {0: 1, 1: 0, 2: 0}.get(x, x)
        assert v(x) + 1 == expected
        counts["exact_G"] += 1
    for x in range(2, 201):
        current = x
        for b in range(301):
            if b >= x - 1:
                assert current == x - b - 2
                counts["orbit_cases"] += 1
            current = v(current)
    all_supports = (
        set(s) for n in range(6) for s in combinations(range(-7, 8), n)
    )
    for support in all_supports:
        exponents = macro(support)
        for x in support:
            assert literal_run(exponents, x) == x - 1
            counts["live_values"] += 1
        if support:
            a, b, c = exponents
            assert a + b + c == 2 * (a + c) - 1
        counts["finite_supports"] += 1
    for support in ({-10003, -10002, -10001}, {10001, 10002, 10003},
                    {-10003, -1, 0, 1, 10003}):
        for x in support:
            assert literal_run(macro(support), x) == x - 1
            counts["live_values"] += 1
        counts["finite_supports"] += 1
    return {"status": "pass", "scope": "finite name-map checks only", **counts}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
