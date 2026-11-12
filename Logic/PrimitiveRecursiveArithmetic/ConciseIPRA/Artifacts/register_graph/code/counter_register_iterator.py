"""Counter-aware J variant and its direct primitive-recursion compiler.

The scalar macros imported below form the counter-independent sublanguage
(replace a scalar body h(r) by a counter body lambda i,r: h(r)). These are
finite standard-model checks, not a proof checker or formal verification.
"""

from __future__ import annotations

from collections.abc import Callable

from register_iterator import C, ONE, P, P2, S, S3


Body = Callable[[int, int], int]


def J(n: int, body: Body) -> int:
    if type(n) is not int or n < 0:
        raise ValueError("the counter must be a natural number")
    register = ONE
    for counter in range(n):
        instruction = body(counter, register)
        if type(instruction) is not int or instruction < 0:
            raise ValueError("an instruction must be a natural number")
        register = register + 1 if instruction == 0 else instruction - 1
    return register


def R(n: int, a: int, body: Body) -> int:
    return J(S(n), lambda i, r: S(C(i, a, body(P(i), r))))


def add(x: int, y: int) -> int:
    return R(y, x, lambda _i, r: S(r))


def multiply(x: int, y: int) -> int:
    return R(y, 0, lambda _i, r: add(r, x))


def factorial(n: int) -> int:
    return R(n, ONE, lambda i, r: multiply(S(i), r))


def J_as_R(n: int, body: Body) -> int:
    return R(n, ONE, lambda i, r: C(body(i, r), S(r), P(body(i, r))))


def run_checks() -> dict[str, object]:
    checked = 0
    for x in range(5):
        for y in range(5):
            assert add(x, y) == x + y
            assert multiply(x, y) == x * y
            checked += 2
    expected_factorials = [1, 1, 2, 6, 24]
    for n, expected in enumerate(expected_factorials):
        assert factorial(n) == expected
        checked += 1
    bodies = {
        "zero": lambda _i, _r: 0,
        "counter": lambda i, _r: i,
        "register": lambda _i, r: r,
        "successor_counter": lambda i, _r: S(i),
        "successor_register": lambda _i, r: S(r),
        "sum": add,
    }
    for name, body in bodies.items():
        for a in range(3):
            expected = a
            for n in range(5):
                assert R(n, a, body) == expected, (name, a, n)
                expected = body(n, expected)
                checked += 1
        for n in range(5):
            assert J_as_R(n, body) == J(n, body), (name, n)
            checked += 1
            value = J(S(n), body)
            old_register = J(n, body)
            instruction = body(n, old_register)
            for target in range(7):
                rhs = (
                    instruction == 0 and target == S(old_register)
                ) or instruction == S(target)
                assert (value == target) == rhs, (name, n, target)
                checked += 1
    return {
        "status": "passed",
        "assertions": checked,
        "arithmetic_argument_range": [0, 4],
        "factorial_range": [0, 4],
        "recursion_initializers": [0, 2],
        "recursion_counters": [0, 4],
        "step_graph_targets": [0, 6],
        "bodies": list(bodies),
        "scope": "finite standard-model checks, not a proof of the metatheorem",
    }


if __name__ == "__main__":
    import json

    print(json.dumps(run_checks(), indent=2))
