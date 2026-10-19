#!/usr/bin/env python3
"""Exact finite check of the proposed clear-top AX simulation prelude.

An experimental source-calculus idea only. It does not build a Turing machine.
State fields are top, cache, stack, additive parameter. Each command's added
parameter is zero, so the additive parameter remains fixed. NIP's native
pre-read halt test is retained.
"""
import json
from itertools import product
from math import isqrt


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def drop(state):
    t, h, w, a = state
    return h, h, pair(t, w), a


def mp0(state):
    t, h, w, a = state
    return (a, 0, pair(0, w), a) if 4 * pair(t, a) == h else (0, 0, w, a)


def nip(state):
    t, h, w, a = state
    if h == 1:
        return None
    new_h, new_w = unpair(w)
    return t, new_h, new_w, a


def prelude(state):
    t, h, w, a = state
    s = nip(mp0(drop(drop(state))))
    assert s is not None
    if h == a == 0:
        s = nip(s)
        assert s is not None
    return s


def run():
    cases = exceptions = growth_checks = 0
    for h, a in product(range(128), repeat=2):
        coded = 4 * pair(h, a)
        assert (coded == h) == (h == a == 0)
        if h or a:
            assert coded > h
        growth_checks += 1
    for t, h, w, a in product(range(12), repeat=4):
        got = prelude((t, h, w, a))
        assert got == (0, h, pair(t, w), a)
        cases += 1
        exceptions += h == a == 0
    return {
        "status": "PASS_EXACT_FINITE_PROTOCOL",
        "prelude_cases": cases,
        "special_case_preludes": exceptions,
        "growth_identity_cases": growth_checks,
        "postcondition": "top=0, cache=old_cache, stack=P(old_top,old_stack), parameter=old_parameter",
        "scope": "Finite exact arithmetic regression of a proposed AX protocol; no unbounded enumerator theorem, literal binary table, or state saving is established.",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
