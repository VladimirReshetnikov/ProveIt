"""Executable standard-model semantics for the proposed register iterator.

This is a semantic illustration, not a proof checker or a proof-assistant
formalization. Every source macro below uses only zero and J; ordinary Python
arithmetic appears only in the interpretation of J and in the test oracles.
"""

from __future__ import annotations

from collections.abc import Callable


Body = Callable[[int], int]


def J(n: int, body: Body) -> int:
    """Start at 1; instruction 0 increments; instruction k+1 loads k."""
    if type(n) is not int or n < 0:
        raise ValueError("the standard numerical domain is the natural numbers")
    register = 1
    for _ in range(n):
        instruction = body(register)
        if type(instruction) is not int or instruction < 0:
            raise ValueError("a numerical body must return a natural number")
        register = register + 1 if instruction == 0 else instruction - 1
    return register


def f(n: int, a: int) -> int:
    return J(n, lambda _u: a)


def S(a: int) -> int:
    return J(a, lambda _u: 0)


ONE = S(0)


def Z(x: int) -> int:
    return f(x, ONE)


def W(x: int) -> int:
    return f(ONE, x)


def D(x: int) -> int:
    return f(x, S(x))


def P(x: int) -> int:
    return W(D(x))


def P2(x: int) -> int:
    return P(P(x))


def S3(x: int) -> int:
    return S(S(S(x)))


def G(c: int, a: int) -> int:
    return P2(f(S(a), Z(c)))


def C(c: int, a: int, b: int) -> int:
    return P2(f(S(a), G(c, S3(b))))


def I(n: int, a: int, body: Body) -> int:
    def instruction(v: int) -> int:
        return S3(C(P(v), a, body(P2(v))))

    return P2(J(S(n), instruction))


def J_as_I(n: int, body: Body) -> int:
    """The proposed inverse translation, expressed through recovered I."""
    return I(n, ONE, lambda v: C(body(v), S(v), P(body(v))))


def run_checks() -> dict[str, object]:
    checked = 0
    max_scalar = 8
    for x in range(max_scalar + 1):
        assert S(x) == x + 1
        assert Z(x) == (1 if x == 0 else 0)
        assert W(x) == (2 if x == 0 else x - 1)
        assert D(x) == (1 if x == 0 else x)
        assert P(x) == max(x - 1, 0)
        checked += 5
    for n in range(max_scalar + 1):
        for a in range(max_scalar + 1):
            assert f(0, a) == ONE
            assert f(n, 0) == S(n)
            assert f(S(n), S(a)) == a
            assert G(n, a) == (0 if n == 0 else a)
            checked += 4
    for c in range(5):
        for a in range(5):
            for b in range(5):
                assert C(c, a, b) == (a if c == 0 else b)
                checked += 1
    bodies = {
        "zero": lambda _u: 0,
        "one": lambda _u: ONE,
        "identity": lambda u: u,
        "successor": S,
        "predecessor": P,
        "zero_test": Z,
    }
    for name, body in bodies.items():
        for a in range(4):
            expected = a
            for n in range(5):
                assert I(n, a, body) == expected, (name, a, n)
                expected = body(expected)
                checked += 1
        for n in range(5):
            assert J_as_I(n, body) == J(n, body), (name, n)
            checked += 1
    return {
        "status": "passed",
        "assertions": checked,
        "scalar_range": [0, max_scalar],
        "selector_range_each_argument": [0, 4],
        "iterator_initializers": [0, 3],
        "iterator_counters": [0, 4],
        "iterator_bodies": list(bodies),
        "scope": "finite standard-model checks, not a proof of the metatheorem",
    }


if __name__ == "__main__":
    import json

    print(json.dumps(run_checks(), indent=2))
