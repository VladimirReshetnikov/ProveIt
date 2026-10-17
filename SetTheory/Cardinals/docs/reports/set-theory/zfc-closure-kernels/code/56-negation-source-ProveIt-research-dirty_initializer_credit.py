#!/usr/bin/env python3
"""Exact finite syntax audit for a wider dirty-root admission rule.

The ordinary proof is in dirty_initializer_credit.md. This file checks its
finite arithmetic inputs; it proves neither the global Enum254 barrier nor
the validity of a new binary initializer. No Lean/Coq build or table edit.

Attribution: intake155/source42's marked NIP-to-DROP argument, original
Enum254 of Mira-Cult/Jeff Ketchersid/Andrew James Wade, and our exact-balance
credit refinement. Pairing and command fields are the original base4 engine.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path


def pair(a: int, b: int) -> int:
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    """Binary-search inverse, independent of the isqrt reference below."""
    lo, hi = 0, n + 1
    while lo + 1 < hi:
        m = (lo + hi) // 2
        if m * (m + 1) // 2 <= n:
            lo = m
        else:
            hi = m
    b = n - lo * (lo + 1) // 2
    return lo - b, b


def reference_unpair(n: int) -> tuple[int, int]:
    d = (isqrt(8 * n + 1) - 1) // 2
    b = n - d * (d + 1) // 2
    return d - b, b


def decode(n: int, inverse=unpair) -> list[tuple[int, ...]]:
    commands = []
    while True:
        old = n
        op, rest = inverse(n)
        fields = []
        for _ in range(3 if op >= 3 else 1):
            x, rest = inverse(rest)
            fields.append(x)
        commands.append((op, *fields))
        if rest == 0:
            return commands
        n = rest - 1
        assert n < old


def encode(commands: list[tuple[int, ...]]) -> int:
    assert commands
    result = None
    for command in reversed(commands):
        rest = 0 if result is None else result + 1
        for field in reversed(command[1:]):
            rest = pair(field, rest)
        result = pair(command[0], rest)
    assert result is not None
    return result


def check(limit: int, credit: int = 8) -> dict:
    if not __debug__:
        raise RuntimeError("Assertions must remain enabled")
    if limit < 1 or not 0 <= credit <= 8:
        raise ValueError("Positive candidate bound and AX-first credit budget 0..8 required")
    drops, images = set(), set()
    d = nip = 0
    minimum = None
    admitted = []
    for n in range(limit):
        commands = decode(n)
        assert commands == decode(n, reference_unpair)
        assert encode(commands) == n
        for i, command in enumerate(commands):
            if command[0] == 2:
                replacement = commands.copy()
                replacement[i] = (1, *command[1:])
                image = (encode(replacement), i)
                assert 0 < image[0] < n
                assert image in drops and image not in images
                images.add(image)
                assert d - nip >= 1
                minimum = d - nip if minimum is None else min(minimum, d - nip)
                nip += 1
            elif command[0] == 1:
                drops.add((n, i))
                d += 1
            assert d >= nip
        op, rest = unpair(n)
        fields = []
        for _ in range(3):
            value, rest = unpair(rest)
            fields.append(value)
        if d - nip <= credit and rest == 0:
            admitted.append({
                "N": n, "next_candidate": n + 1,
                "balance_B_next": d - nip,
                "minimum_AXIOM_selector_A": max(0, 3 - op),
                "AX_parameters_x_y_u": fields,
                "remaining_proof_list": rest,
            })
    return {
        "scope": "Finite exact command-code/count audit. No global scheduler, binary initializer, state reduction, or PA endpoint proof.",
        "candidate_bound_exclusive": limit, "initial_safe_prefix_credit": credit,
        "command_zero": list(decode(0)[0]),
        "drop_occurrences": d, "nip_occurrences": nip,
        "checked_marked_images": len(images), "all_images_strictly_positive": True,
        "minimum_global_pre_NIP_balance": minimum,
        "eligible_N_below_bound": admitted,
        "eligible_count": len(admitted),
        "largest_eligible_N_below_bound": max((row["N"] for row in admitted), default=None),
        "family": {
            "logical_register_order": ["N", "T", "W", "A", "D", "H", "X", "Y", "L"],
            "zero_fields": ["X", "Y", "L"],
            "free_fields": ["T", "W", "D", "H"],
            "other_conditions": "N and A satisfy one listed eligible row; actual empty program counter at root.",
            "after_first_AX": "PL0, NP=N+1; top=gate(D+x,H+y,A+fst(unP N)-3), D=H=0; first8 stack entries are unconditional logical axiom instances.",
            "dirty_tail": "GEN(oldH), oldTW, oldWS may all be dirty; remaining_proof_list=0 does not require theorem-stack tail=0.",
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidates", type=int, default=100000)
    parser.add_argument("--credit", type=int, default=8,
                        help="Conservative budget 0..8 for the eight guaranteed safe AX rows")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = check(args.candidates, args.credit)
    result["driver_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in (
        "candidate_bound_exclusive", "eligible_count", "largest_eligible_N_below_bound",
        "checked_marked_images", "minimum_global_pre_NIP_balance")}, indent=2))


if __name__ == "__main__":
    main()
