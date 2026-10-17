#!/usr/bin/env python3
"""Independent exact-integer checks of the source-level AX/MP rewrite.

This uses the literal Cantor pairing and formula-code equations from Code254,
not the register compiler or a symbolic arithmetic oracle. All AX commands in
this bounded suite take the unchanged zero-gate branch. That avoids enormous
bundle integers while testing the new stack effects and all proof-block
interfaces. It does not prove binary simulation, startup, or the theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import dataclass
from pathlib import Path
import time


def pair(x: int, y: int) -> int:
    s = x + y
    return s * (s + 1) // 2 + y


def unpair(z: int) -> tuple[int, int]:
    s = (math.isqrt(8 * z + 1) - 1) // 2
    y = z - s * (s + 1) // 2
    return s - y, y


def imp(a: int, b: int) -> int:
    return 4 * pair(a, b)


def rel(a: int, b: int) -> int:
    return 4 * pair(a, b) + 1


def all_(a: int, b: int) -> int:
    return 4 * pair(a, b) + 2


def eq(a: int, b: int) -> int:
    return 4 * pair(a, b) + 3


def neg(a: int) -> int:
    return imp(a, 1)


def exists(a: int, b: int) -> int:
    return neg(all_(a, neg(b)))


def rows(a: int, h: int, b: int, c: int, u: int, binder: int) -> list[int]:
    """The eight original logical rows, then the indicated GEN row."""
    return [
        exists(a, eq(a, b)),
        imp(all_(a, imp(b, c)), imp(all_(a, b), all_(a, c))),
        imp(eq(a, b), imp(rel(c, a), rel(c, b))),
        imp(all_(a, all_(b, c)), all_(b, all_(a, c))),
        imp(eq(c, a), imp(rel(c, b), rel(a, b))),
        imp(exists(a, all_(a, b)), b),
        imp(eq(c, a), imp(eq(c, b), eq(a, b))),
        imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c))),
        all_(binder, h),
    ]


def push_list(xs: list[int], s: int) -> int:
    for x in reversed(xs):
        s = pair(x, s)
    return s


@dataclass(frozen=True)
class W:
    t: int
    s: int
    d: int
    h: int


D = ("drop", 0)
N = ("nip", 0)


def nips(k: int) -> list[tuple]:
    return [N] * k


class Interpreter:
    def __init__(self, shifted_ax: bool, delta: int, consume_cache: bool = False):
        self.shifted_ax = shifted_ax
        self.delta = delta
        self.consume_cache = consume_cache
        self.commands = 0
        self.maximum_integer_bits = 0

    def step(self, command: tuple, w: W) -> W | None:
        self.commands += 1
        self.maximum_integer_bits = max(
            self.maximum_integer_bits,
            *(z.bit_length() for z in (w.t, w.s, w.d, w.h)),
        )
        tag, *args = command
        if tag == "drop":
            (x,) = args
            return W(w.h, pair(w.t, w.s), w.d + x, 0 if self.consume_cache else w.h)
        if tag == "nip":
            (x,) = args
            if w.h == 1:
                return None
            top, tail = unpair(w.s)
            return W(w.t, tail, w.d + x, top)
        if tag == "mp":
            (x,) = args
            target = w.d + x
            if imp(w.t, target) == w.h:
                stack = pair(0, w.s) if self.delta else w.s
                return W(target, stack, target, 0)
            return W(0, w.s, target, 0)
        if tag == "ax":
            c, x, y, u = args
            a, b = w.d + x, w.h + y
            if c != a and c != b:
                raise ValueError("This exact bounded suite only uses zero-gate AX cases")
            binder = a + w.t if self.shifted_ax else a
            emitted = rows(a, w.h, b, c, u, binder)
            if not self.shifted_ax:
                emitted.append(w.t)
            return W(0, push_list(emitted, w.s), 0, 0)
        raise ValueError(tag)

    def run(self, program: list[tuple], w: W) -> W | None:
        for command in program:
            w = self.step(command, w)
            if w is None:
                return None
        return w


def discard(shifted: bool) -> list[tuple]:
    preparation = [("mp", 1)] + ([D] if shifted else [])
    return preparation + [("ax", 1, 0, 0, 0)] + nips(10)


def leaf(shifted: bool, j: int, a: int, b: int, u: int) -> list[tuple]:
    # Set c=a only to make the (unchanged) bundle gate zero in this bounded test.
    preparation = discard(shifted) + ([D] if shifted else [])
    return preparation + [("ax", a, a, b, u)] + nips(j) + [D] + nips(11 - j)


def gen_suffix(shifted: bool, i: int) -> list[tuple]:
    suffix = [D, N, ("ax", i, i, 0, 0)] + nips(9) + [D]
    return suffix + nips(1 if shifted else 2)


def mp_suffix(shifted: bool, delta: int, b: int) -> list[tuple]:
    """Begin after p_I, with I(A,B) current and A saved above the old S."""
    prefix = [N, D, N, ("mp", b)]
    if shifted:
        prefix.append(D)
    return prefix + [("ax", b, 0, 0, 0)] + nips(10) + [D] + nips(1 + delta)


def verify() -> dict:
    started = time.perf_counter()
    records = []
    # Parameter sizes are deliberately small; all executed arithmetic is exact.
    # Stacks may encode arbitrary entries, testing preservation rather than
    # assuming that the initial stack is all zero or derivable.
    starts = [(0, 0), (2, 7), (5, pair(3, 11))]
    gen_inputs = [(0, 0), (1, 1), (2, 3), (7, 0)]
    mp_inputs = [(0, 0), (0, 2), (2, 0), (2, 3), (1, 4), (4, 1)]

    variants = [(a, d, consume) for a, d in
                [(False, 1), (False, 0), (True, 1), (True, 0)]
                for consume in [False, True]]
    for shifted, delta, consume in variants:
        vm = Interpreter(shifted, delta, consume)
        counts = {"normalization": 0, "row_extraction": 0, "generalization": 0,
                  "modus_ponens": 0, "actual_ax_effect": 0,
                  "falsity_detector": 0, "actual_drop_effect": 0}
        for t, s in starts:
            assert vm.run(discard(shifted), W(t, s, 0, 0)) == W(0, s, 0, 0)
            counts["normalization"] += 1

        for a, b, u in [(0, 0, 0), (1, 2, 1)]:
            expected_rows = rows(a, 0, b, a, u, a)
            for j in range(1, 9):
                t, s = starts[j % len(starts)]
                actual = vm.run(leaf(shifted, j, a, b, u), W(t, s, 0, 0))
                assert actual == W(expected_rows[j - 1], s, 0, 0), (shifted, delta, j)
                counts["row_extraction"] += 1

        for h, i in gen_inputs:
            s = pair(2, 9)
            assert vm.run(gen_suffix(shifted, i), W(h, s, 0, 0)) == W(all_(i, h), s, 0, 0)
            counts["generalization"] += 1

        for a, b in mp_inputs:
            s = pair(5, 13)
            actual = vm.run(mp_suffix(shifted, delta, b), W(imp(a, b), pair(a, s), 0, 0))
            if (a == 1 or b == 1) and not consume:
                assert actual is None, (shifted, delta, a, b)
            else:
                assert actual == W(b, s, 0, 0), (shifted, delta, a, b)
            counts["modus_ponens"] += 1

        # This explicitly checks a dirty old T. Shifted AX retains its numeric
        # contribution only in GEN's variable label, and does not save old T.
        before = W(3, pair(4, 6), 1, 2)
        after = vm.step(("ax", 1, 0, 0, 1), before)
        assert after is not None and (after.t, after.d, after.h) == (0, 0, 0)
        stack = after.s
        popped = []
        for _ in range(9 + (not shifted)):
            top, stack = unpair(stack)
            popped.append(top)
        expected = rows(1, 2, 2, 1, 1, 4 if shifted else 1)
        if not shifted:
            expected.append(3)
        assert popped == expected and stack == before.s
        counts["actual_ax_effect"] += 1

        assert vm.run([D, N, N], W(1, pair(4, 7), 0, 0)) is None
        counts["falsity_detector"] += 1
        before_drop = W(3, pair(4, 6), 5, 2)
        assert vm.step(("drop", 7), before_drop) == W(
            2, pair(3, before_drop.s), 12, 0 if consume else 2)
        counts["actual_drop_effect"] += 1
        records.append({
            "ax": "destructive_shifted_binder" if shifted else "original",
            "mp_zero_push": delta,
            "drop_consumes_cache": consume,
            "checks": counts,
            "exact_command_steps": vm.commands,
            "largest_integer_bits": vm.maximum_integer_bits,
        })

    return {
        "status": "PASS",
        "arithmetic": "Exact Python integers, literal Cantor pairing, exact integer square roots",
        "source_pin": "43026ff42f0939f09b9e95495248cfadcad38e38",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "variants": records,
        "total_contract_checks": sum(sum(r["checks"].values()) for r in records),
        "elapsed_seconds": round(time.perf_counter() - started, 6),
        "scope": [
            "Bounded exact tests supplement the separately supplied universal mathematical proof.",
            "AX tests use the unchanged zero-gate branch; no positive bundle test is claimed.",
            "No compiled binary table or blank startup is checked here.",
            "The old AX/old MP combination is included as a control.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = verify()
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
