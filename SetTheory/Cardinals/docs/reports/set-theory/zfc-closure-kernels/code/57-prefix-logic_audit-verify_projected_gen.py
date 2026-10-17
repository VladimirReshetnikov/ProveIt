#!/usr/bin/env python3
"""Independent exact checks of the dirty-cache projected GEN prefix.

The prefix interpreter executes individual decrement/increment effects of
the proposed unpair loop and original macros122,211,162,117,159. Whole AX
tests use literal Code254 arithmetic on the unchanged eight rows and the
zero gate. This does not inspect or certify the compiled binary table.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from verify_source_rewrite import (
    D, N, Interpreter, W, all_, discard, imp, leaf, mp_suffix,
    nips, pair, push_list, rows, unpair,
)


def literal_prefix(t: int, h: int) -> tuple[int, int, int, int]:
    x = y = 0
    # New unpair-T root around the literal inverse-walk body154.
    while t:
        t -= 1
        y += 1
        if x:
            x -= 1
        else:
            while y:
                y -= 1
                x += 1
    # Original122: copy loop200 followed by restore loop207.
    while h:
        h -= 1
        x += 1
        t += 1
    while x:
        x -= 1
        h += 1
    # Original211.
    while y:
        y -= 1
        x += 1
    # Original pair162, including its internal copy215 and transfer208.
    while True:
        while t:
            t -= 1
            x += 1
            y += 1
        if not x:
            break
        x -= 1
        y += 1
        while x:
            x -= 1
            t += 1
    # Original times4_117 and add2_159.
    while y:
        y -= 1
        t += 4
    t += 2
    return t, h, x, y


class ProjectedInterpreter(Interpreter):
    def __init__(self, delta: int, consume_cache: bool):
        super().__init__(True, delta, consume_cache)

    def step(self, command: tuple, w: W) -> W | None:
        if command[0] != "ax":
            return super().step(command, w)
        self.commands += 1
        self.maximum_integer_bits = max(
            self.maximum_integer_bits,
            *(n.bit_length() for n in (w.t, w.s, w.d, w.h)),
        )
        _, c, x, y, u = command
        i, j = unpair(w.t)
        a, b = w.d + x, w.h + i + y
        if c != a and c != b:
            raise ValueError("Bounded suite deliberately uses the zero bundle gate")
        emitted = rows(a, w.h, b, c, u, j)
        return W(0, push_list(emitted, w.s), 0, 0)


def verify() -> dict:
    prefix_cases = 0
    for i in range(8):
        for j in range(8):
            for h in [0, 1, 2, 5, 11]:
                u = pair(i, j)
                assert literal_prefix(u, h) == (all_(j, h), h + i, 0, 0)
                prefix_cases += 1
    identity_cases = 0
    for i in list(range(128)) + [1024, 65536, 10**20]:
        assert imp(i, 0) == pair(i, i)
        assert unpair(imp(i, 0)) == (i, i)
        identity_cases += 1

    records = []
    for delta in [0, 1]:
        for consume in [False, True]:
            vm = ProjectedInterpreter(delta, consume)
            checks = {"normalization": 0, "row_extraction": 0,
                      "generalization_suffix": 0, "modus_ponens": 0,
                      "dirty_cache_offset": 0, "falsity_detector": 0}
            for t, s in [(0, 0), (2, 7), (5, pair(3, 11))]:
                assert vm.run(discard(True), W(t, s, 0, 0)) == W(0, s, 0, 0)
                checks["normalization"] += 1
            for a, b, u in [(0, 0, 0), (1, 2, 1)]:
                expected = rows(a, 0, b, a, u, 0)
                for j in range(1, 9):
                    s = pair(2, 9)
                    assert vm.run(leaf(True, j, a, b, u), W(3, s, 0, 0)) == W(
                        expected[j - 1], s, 0, 0)
                    checks["row_extraction"] += 1
            for h, j in [(0, 0), (1, 1), (2, 3), (7, 0), (2, 5)]:
                s = pair(2, 9)
                # Start after the proved q_j block, with H saved below it.
                before = W(imp(j, 0), pair(h, s), 0, 0)
                suffix = [N, ("ax", 0, 0, 0, 0)] + nips(9) + [D, N]
                assert vm.run(suffix, before) == W(all_(j, h), s, 0, 0)
                checks["generalization_suffix"] += 1
            for a, b in [(0, 0), (0, 2), (2, 0), (2, 3), (1, 4), (4, 1)]:
                s = pair(5, 13)
                result = vm.run(mp_suffix(True, delta, b),
                                W(imp(a, b), pair(a, s), 0, 0))
                if (a == 1 or b == 1) and not consume:
                    assert result is None
                else:
                    assert result == W(b, s, 0, 0)
                checks["modus_ponens"] += 1
            for i, j, h in [(0, 0, 0), (1, 2, 3), (3, 1, 2)]:
                s = pair(3, 7)
                # c=a=1 makes the gate zero even with the actual shifted b.
                result = vm.step(("ax", 1, 0, 2, 0), W(pair(i, j), s, 1, h))
                expected = rows(1, h, h + i + 2, 1, 0, j)
                assert result == W(0, push_list(expected, s), 0, 0)
                checks["dirty_cache_offset"] += 1
            assert vm.run([D, N, N], W(1, pair(4, 7), 0, 0)) is None
            checks["falsity_detector"] += 1
            records.append({
                "mp_zero_push": delta,
                "drop_consumes_cache": consume,
                "checks": checks,
                "exact_commands": vm.commands,
                "maximum_integer_bits": vm.maximum_integer_bits,
            })
    return {
        "status": "passed",
        "literal_prefix_cases": prefix_cases,
        "projection_identity_cases": identity_cases,
        "source_contract_cases": sum(sum(r["checks"].values()) for r in records),
        "variants": records,
        "all_AX_cases_use_zero_gate": True,
        "compiled_binary_table_verified": False,
        "new_source_DAG_control_levels_verified": False,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = verify()
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")
