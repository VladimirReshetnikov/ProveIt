#!/usr/bin/env python3
"""Exact symbolic contracts for reordered complete AX outputs.

This validates the abstract stack interface, not a TM or numeric-code decoder.
No probabilistic fingerprints or bounded approximations are used.
"""
from __future__ import annotations

from dataclasses import dataclass
import itertools
import json
from pathlib import Path
import time


@dataclass(frozen=True)
class State:
    top: object
    stack: tuple
    datum: object = 0
    cache: object = 0


def imp(a, b):
    return 0 if a == b == 0 else ("imp", a, b)


def plus(a, b):
    if a == 0:
        return b
    if b == 0:
        return a
    if isinstance(a, int) and isinstance(b, int):
        return a + b
    return ("add", a, b)


def step(s, cmd):
    if cmd == "D":
        return State(s.cache, (s.top,) + s.stack, s.datum, s.cache)
    if cmd == "N":
        if s.cache == 1:
            return None
        assert s.stack, "Attempted to inspect the arbitrary protected suffix"
        return State(s.top, s.stack[1:], s.datum, s.stack[0])
    _, x = cmd
    b = plus(s.datum, x)
    success = s.cache == imp(s.top, b)
    return State(b if success else 0, ((0,) + s.stack) if success else s.stack, b, 0)


def run(s, commands):
    for cmd in commands:
        if s is None:
            return None
        s = step(s, cmd)
    return s


def select(j, m=10):
    assert 1 <= j <= m
    return ["N"] * m if j == m else ["N"] * (m-j) + ["D"] + ["N"] * (j+1)


def emit(s, order, c, x=0, y=0, u=0):
    """Abstract original AX output interface, represented by exact term trees."""
    a, b = plus(s.datum, x), plus(s.cache, y)
    values = {
        "GEN": ("all", a, s.cache),
        "BUNDLE": 0 if c == a or c == b else ("bundle", a, b, c),
        **{k: (k, a, b, c, u) for k in range(1, 9)},
    }
    rows = [values[k] for k in order]
    return State(rows[-1], tuple(reversed(rows[:-1])) + (s.top,) + s.stack)


def ax_then_select(s, order, item, c, x=0, y=0, u=0):
    return run(emit(s, order, c, x, y, u), select(order.index(item)+1))


def discard(s, order):
    s = step(s, ("MP", 1))
    return ax_then_select(s, order, "BUNDLE", 1)


def blocks(order):
    # A marked tail remains wholly opaque: exact tuple identity is asserted.
    suffix = (("arbitrary", "one"), ("arbitrary", "two"))
    d = discard(State(("arbitrary", "top"), suffix), order)
    assert d == State(0, suffix)
    # Treat Build_H as its induction hypothesis and execute the GEN wrapper.
    h = ("derived", "H")
    g = run(State(h, suffix), ["D", "N"])
    g = ax_then_select(g, order, "GEN", 7, x=7)
    assert g == State(("all", 7, h), suffix)
    # Treat both recursive Build calls as their exact induction hypotheses.
    a, b = ("derived", "A"), ("derived", "B")
    s = step(State(a, suffix), "D")
    s = State(imp(a, b), s.stack)  # Build(A -> B), retaining the saved A.
    s = run(s, ["N", "D", "N", ("MP", b)])
    assert s == State(b, (0,) + suffix, b, 0)
    s = ax_then_select(s, order, "BUNDLE", b)
    assert s == State(0, (0,) + suffix, 0, b)
    assert run(s, ["D", "N", "N"]) == State(b, suffix)
    # The refutation suffix uses exactly the original NIP-before-pop halt test.
    assert run(State(1, suffix), ["D", "N", "N"]) is None


def main():
    started = time.monotonic()
    contracts = orders = early_cases = 0
    suffix = (("opaque", 0), ("opaque", 1))
    old = ("arbitrary", "old current")
    # General-position evidence also moves GEN/bundle to every possible slot.
    for shift in range(10):
        order = tuple(range(shift, 10)) + tuple(range(shift))
        rows = tuple(("output", k) for k in order)
        for j in range(1, 11):
            s = State(rows[-1], tuple(reversed(rows[:-1])) + (old,) + suffix)
            assert run(s, select(j)) == State(rows[j-1], suffix, 0, old)
            for fpos in range(11):
                rr = list(rows)
                tt = old
                if fpos < 10:
                    rr[fpos] = 1
                else:
                    tt = 1
                ss = State(rr[-1], tuple(reversed(rr[:-1])) + (tt,) + suffix)
                out = run(ss, select(j))
                assert out is None or out == State(rr[j-1], suffix, 0, tt)
                early_cases += 1
    for p in itertools.permutations(range(1, 9)):
        order = ("GEN",) + p + ("BUNDLE",)
        rows = tuple(("output", k) for k in order)
        for j in range(1, 11):
            s = State(rows[-1], tuple(reversed(rows[:-1])) + (old,) + suffix)
            assert run(s, select(j)) == State(rows[j-1], suffix, 0, old)
            contracts += 1
        blocks(order)
        orders += 1
    result = {
        "all_checks_passed": True,
        "actual_eight_row_permutations": orders,
        "selection_contracts": contracts,
        "general_output_rotations": 10,
        "early_halt_or_selection_cases": early_cases,
        "discard_gen_mp_and_final_suffix_permutations": orders,
        "evidence_scope": "exact symbolic abstract-enumerator command contracts",
        "numeric_decoder_or_binary_TM_checked": False,
        "seconds": round(time.monotonic()-started, 3),
    }
    target = Path(__file__).with_name("axiom_row_permutation_checks.json")
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
