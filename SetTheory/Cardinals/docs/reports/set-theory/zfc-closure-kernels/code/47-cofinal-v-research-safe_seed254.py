#!/usr/bin/env python3
"""Recognize a sufficient, proof-carrying family of initial formula data.

Certificate constructors correspond to SeedInvariant254.Formula. This is not a
complete theorem prover. A rejected number may still be a theorem. Stack cells
use unshifted Cantor pairing; adding one would give a different, unsafe test.
"""
from __future__ import annotations

from math import isqrt


def pair(a: int, b: int) -> int:
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    if type(n) is not int or n < 0:
        raise ValueError("natural number required")
    d = (isqrt(8 * n + 1) - 1) // 2
    b = n - d * (d + 1) // 2
    return d - b, b


def code(p: tuple) -> int:
    tag, *args = p
    if tag == "truth":
        return 0
    a = args[0]
    if tag == "all":
        return 4 * pair(a, code(args[1])) + 2
    if tag == "identity":
        return 4 * pair(a, a)
    if tag == "weaken":
        return 4 * pair(a, code(args[1]))
    if tag == "exfalso":
        return 4 * pair(1, a)
    if tag == "eqRefl":
        return 4 * pair(a, a) + 3
    raise ValueError("unknown certificate constructor")


def formula(n: int, fuel: int = 256) -> tuple | None:
    """Return a finite certificate, with no search or theorem oracle."""
    if type(n) is not int or n < 0:
        raise ValueError("natural formula code required")
    if n == 0:
        return ("truth",)
    if fuel <= 0:
        return None
    a, b = unpair(n // 4)
    tag = n % 4
    result = None
    if tag == 3 and a == b:
        result = ("eqRefl", a)
    elif tag == 2:
        inner = formula(b, fuel - 1)
        if inner is not None:
            result = ("all", a, inner)
    elif tag == 0:
        if a == b:
            result = ("identity", a)
        elif a == 1:
            result = ("exfalso", b)
        else:
            inner = formula(b, fuel - 1)
            if inner is not None:
                result = ("weaken", a, inner)
    if result is not None and code(result) != n:
        raise AssertionError("certificate/code disagreement")
    return result


def stack_code(ps: list[tuple]) -> int:
    n = 0
    for p in reversed(ps):
        n = pair(code(p), n)
    return n


def stack(n: int, fuel: int = 256) -> list[tuple] | None:
    """Decode all cells, including buried entries, of an unshifted stack."""
    if type(n) is not int or n < 0:
        raise ValueError("natural stack code required")
    original, ps = n, []
    while n:
        if len(ps) >= fuel:
            return None
        head, tail = unpair(n)
        p = formula(head, fuel)
        if p is None:
            return None
        if tail >= n:
            raise AssertionError("stack tail must decrease")
        ps.append(p)
        n = tail
    if stack_code(ps) != original:
        raise AssertionError("stack certificate/code disagreement")
    return ps


def state(logical: list[int]) -> dict | None:
    """AS order N,T,W,A,D,H,X,Y,L; a whole binary frame is a separate check."""
    if len(logical) != 9 or any(type(n) is not int or n < 0 for n in logical):
        raise ValueError("exactly nine natural logical registers required")
    top, cache, entries = formula(logical[1]), formula(logical[5]), stack(logical[2])
    if top is None or cache is None or entries is None:
        return None
    return {"top": top, "cache": cache, "stack": entries}


def check() -> dict:
    # Every accepted certificate reconstructs the exact input. No claim that
    # this bounded census proves the Lean theorem or all-formula completeness.
    count_formula = count_stack = 0
    for n in range(65536):
        p, ps = formula(n), stack(n)
        if p is not None:
            assert code(p) == n
            count_formula += 1
        if ps is not None:
            assert stack_code(ps) == n
            count_stack += 1
    assert formula(1) is None
    assert stack(1) is None
    assert stack(60) is None  # [5,0,0,1], not a harmless scratch value.
    assert code(formula(3)) == 3
    assert code(formula(6)) == 6
    assert stack_code(stack(3)) == 3
    assert stack_code(stack(9)) == 9
    assert state([999, 3, 9, 8, 7, 6, 5, 4, 3]) is not None
    assert state([0, 0, 60, 0, 0, 0, 0, 0, 0]) is None
    return {"scope": "finite certificate/code checks, not binary simulation",
            "inputs_each": 65536, "accepted_formula_codes": count_formula,
            "accepted_stack_codes": count_stack,
            "falsity_and_buried_falsity_rejected": True}


if __name__ == "__main__":
    import json
    if not __debug__:
        raise SystemExit("run with assertions enabled")
    print(json.dumps(check(), indent=2))
