#!/usr/bin/env python3
"""Check the residual-parameter compiler's command/stack contracts.

This is an exact integer model of DROP, NIP, MP, the two parameter formulas,
and the AX stack interface.  Native rho/bundle expressions are deliberately
abstracted by several safe (non-1) numerical instantiations.  The mathematical
proof only needs their non-1 property and their displayed order; this test is
not a replay of the enormous native AX emitter or a binary-machine proof.

In the GEN/MP induction tests, a HOLE represents an already-compiled premise
and satisfies exactly its stated universal block contract.  HOLE is a test
operation, not an instruction claimed to occur in the resulting machine.

Python 3 standard library only.  No floating point or code fingerprints.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from pathlib import Path
from math import isqrt
import json
import sys


def pair(a: int, b: int) -> int:
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def imp(a: int, b: int) -> int:
    return 4 * pair(a, b)


def quant(i: int, a: int) -> int:
    return 4 * pair(i, a) + 2


def push(xs: tuple[int, ...], s: int) -> int:
    for x in reversed(xs):
        s = pair(x, s)
    return s


@dataclass(frozen=True)
class State:
    t: int
    s: int
    d: int
    h: int


N = ("NIP",)
D = ("DROP",)
M = ("MP",)


def ax(c: int, y: int, x: int) -> tuple:
    return ("AX", c, y, x)


def rows(mode: int, a: int, b: int, c: int, u: int) -> tuple[int, ...]:
    # Three independent instantiations of the only required interface:
    # eight ordered native row values, each a multiple of four.
    if mode == 0:
        return (0,) * 8
    if mode == 1:
        return tuple(4 * (j + 1) for j in range(8))
    return tuple(4 * (1 + (j + 1) * (a + 2*b + 3*c + 5*u + 1)) for j in range(8))


def bundle(mode: int, a: int, b: int, c: int) -> int:
    return 0 if mode == 0 else 4 * (mode + a + 2*b + 3*c)


def step(command: tuple, w: State, mode: int = 0, opposite: bool = False) -> State | None:
    t, s, d, h = w.t, w.s, w.d, w.h
    match command:
        case ("DROP",):
            return State(h, pair(t, s), d, h)
        case ("NIP",):
            if h == 1:
                return None
            top, rest = unpair(s)
            return State(t, rest, d, top)
        case ("MP",):
            return State(d, pair(0, s), d, 0) if imp(t, d) == h else State(0, s, d, 0)
        case ("AX", c, y, x):
            a, b, u = x, h + y, d
            rr = rows(mode, a, b, c, u) + (quant(u, h), t)
            g = 0 if c == a or c == b else bundle(mode, a, b, c)
            residual = max(c-a-1, 0) if opposite else max(a-c-1, 0)
            return State(g, push(rr, s), residual, 0)
        case ("HOLE", target, output_parameter):
            return State(target, s, output_parameter, 0)
        case _:
            raise AssertionError(command)


def run(commands: list[tuple], w: State, mode: int = 0, opposite: bool = False) -> State | None:
    for command in commands:
        w = step(command, w, mode, opposite)
        if w is None:
            return None
    return w


def reset() -> list[tuple]:
    return ([ax(0, 0, 0)] + [N] * 10) * 2


def setter(v: int, opposite: bool = False) -> list[tuple]:
    setting_ax = ax(v+1, v+1, 0) if opposite else ax(0, 0, v+1)
    return [setting_ax] + [N] * 10 + [D, N]


def leaf(j: int, a: int, b: int, c: int, u: int) -> list[tuple]:
    assert 1 <= j <= 8
    return reset() + setter(u) + [ax(c, b, a)] + [N]*j + [D] + [N]*(11-j)


def bundle_leaf(a: int, b: int, c: int) -> list[tuple]:
    assert c != a and c != b
    return reset() + [ax(c, b, a)] + [N]*10


def gen_block(i: int, proof: list[tuple]) -> list[tuple]:
    return proof + setter(i) + [D, N, ax(0, 0, 0)] + [N]*9 + [D, N, N]


def mp_block(b: int, pa: list[tuple], pab: list[tuple]) -> list[tuple]:
    return pa + [D] + pab + setter(b) + [N, D, N, M, N]


def pack(command: tuple, tail: int) -> int:
    match command:
        case ("MP",):
            return pair(0, tail)
        case ("DROP",):
            return pair(1, tail)
        case ("NIP",):
            return pair(2, tail)
        case ("AX", c, y, x):
            return pair(c+3, pair(y, pair(x, tail)))
        case _:
            raise AssertionError(command)


def read_command(raw: int) -> tuple[tuple, int]:
    tag, tail = unpair(raw)
    if tag < 3:
        return (M, D, N)[tag], tail
    y, tail = unpair(tail)
    x, tail = unpair(tail)
    return ax(tag-3, y, x), tail


def cursor(commands: list[tuple]) -> int:
    n = 0
    for command in reversed(commands):
        n = 1 + pack(command, n)
    return n


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run this checker without -O: its assertions are the checks.")
    counts = {}
    # Include nil, its zero-push alias, falsity below the protected boundary,
    # and a mixed stack; protected entries must never be inspected/changed.
    stacks = (0, pair(1, 0), push((7, 1, 0), 0))
    initials = [State(t, s, d, h) for t, d, h, s in product(range(3), range(3), range(3), stacks)]
    cases = 0
    for mode, w in product(range(3), initials):
        assert run(reset(), w, mode) == State(0, w.s, 0, 0)
        cases += 1
    counts["reset"] = cases

    cases = 0
    for mode, t, d, s, v in product(range(3), range(4), range(3), stacks, range(4)):
        got = run(setter(v), State(t, s, d, 0), mode)
        assert got == (None if t == 1 else State(t, s, v, 0))
        cases += 1
    counts["setter"] = cases

    cases = 0
    for mode, t, d, s, v in product(range(3), range(4), range(3), stacks, range(4)):
        got = run(setter(v, opposite=True), State(t, s, d, 0), mode, opposite=True)
        assert got == (None if t == 1 else State(t, s, v, 0))
        cases += 1
    counts["opposite_residual_setter"] = cases

    cases = 0
    samples = ((0, 0, 0, 0), (1, 0, 2, 3), (3, 2, 1, 0), (0, 1, 3, 2))
    for mode, w, params, j in product(range(3), initials[::10], samples, range(1, 9)):
        a, b, c, u = params
        expected = rows(mode, a, b, c, u)[j-1]
        assert run(leaf(j, a, b, c, u), w, mode) == State(expected, w.s, max(a-c-1, 0), 0)
        cases += 1
    counts["row_selection"] = cases

    cases = 0
    for mode, w, (a, b, c) in product(range(3), initials[::10], ((0, 0, 1), (1, 2, 0), (2, 3, 1))):
        expected = bundle(mode, a, b, c)
        assert run(bundle_leaf(a, b, c), w, mode) == State(expected, w.s, max(a-c-1, 0), 0)
        cases += 1
    counts["bundle_selection"] = cases

    cases = 0
    for mode, w, h, i, dp in product(range(3), initials[::10], range(4), range(3), range(2)):
        p = [("HOLE", h, dp)]
        got = run(gen_block(i, p), w, mode)
        assert got == (None if h == 1 else State(quant(i, h), w.s, 0, 0))
        cases += 1
    counts["generalization_inductive_step"] = cases

    cases = 0
    for mode, w, a, b, d1, d2 in product(range(3), initials[::10], range(4), range(4), range(2), range(2)):
        pa, pab = [("HOLE", a, d1)], [("HOLE", imp(a, b), d2)]
        got = run(mp_block(b, pa, pab), w, mode)
        assert got == (None if a == 1 else State(b, w.s, b, 0))
        cases += 1
    counts["modus_ponens_inductive_step"] = cases

    cases = 0
    for mode, s, d in product(range(3), stacks, range(4)):
        assert run([D, N, N], State(1, s, d, 0), mode) is None
        cases += 1
    counts["terminal_refutation_detection"] = cases

    cases = 0
    small_commands = [M, D, N, ax(0, 0, 0), ax(1, 2, 3)]
    for k in range(1, 4):
        for commands0 in product(small_commands, repeat=k):
            commands = list(commands0)
            n = cursor(commands)
            assert n > 0
            for expected in commands:
                command, rest = read_command(n-1)
                assert command == expected and rest < n
                n = rest
            assert n == 0
            cases += 1
    assert cursor([M]) == 1
    assert pair(0, 0) == 0 and unpair(pair(0, 0)) == (0, 0)
    counts["wire_roundtrip_and_cursor_decrease"] = cases

    result = {
        "status": "PASS",
        "residual": "max(A-C-1,0); opposite setter also checked with max(C-A-1,0)",
        "tests": counts,
        "total_tests": sum(counts.values()),
        "arithmetic": "exact Python integers; integer square-root Cantor inverse",
        "scope": [
            "DROP/NIP/MP and AX ordered-stack interface",
            "Three safe-row instantiations, including all-zero aliases",
            "RESET, SET, all eight row positions, bundle, GEN/MP induction macros",
            "Protected stacks containing falsity and the P(0,0)=0 alias",
            "Variable-field command packing and decreasing continuation cursor"
        ],
        "not_claimed": [
            "Evaluation or proof of the literal native AX row/bundle generator",
            "Verification that source splices implement this interpreter",
            "Machine-checked universal mathematical theorem",
            "Binary TM runtime correctness or a smaller working-state count"
        ]
    }
    output = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name("residual_contracts_check.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
