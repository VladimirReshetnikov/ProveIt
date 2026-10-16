#!/usr/bin/env python3
"""Reproduce the independently run extra quantified-NAND checks.

This preserves the checks executed during the machine agent's second audit:
16 gapped-parameter matrices, 256 direct-EPSC-versus-wrapper comparisons,
every bit string of length at most 13, and the first 255 shortlex words.

The finite semantic evaluator and direct source-EPSC equation are imported
from the separately maintained test_qnand.py. The EPSC builder, codec and
enumeration expression come from qnand.py. Neither evaluator is on the
public acceptance path. These are finite diagnostics, not a consistency
or machine-correctness proof. Python's standard library is sufficient.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import qnand as q
from test_qnand import FiniteEvaluator, direct_epsc


def run():
    if not __debug__:
        raise RuntimeError("Run without -O: assertions perform the audit checks")

    comparisons = 0
    cases = []
    for gap in (2, 3, 4, 5):
        arena = q.Arena()
        formulas = [
            arena.rel(0, gap),
            arena.rel(gap, 1),
            arena.q(arena.rel(1, gap + 1), arena.rel(gap + 1, 2)),
            arena.q(arena.rel(0, gap + 1),
                    arena.q(arena.rel(2, gap + 2), arena.rel(1, 3))),
        ]
        for matrix in formulas:
            root = q.epsc(arena, matrix)
            width = max(2, arena.need[matrix])
            assert arena.need[root] == 0
            for mask in range(16):
                evaluator = FiniteEvaluator(arena, range(2), mask)
                expected = all(
                    direct_epsc(evaluator, matrix, parameters)
                    for parameters in itertools.product(
                        range(2), repeat=width - 2)
                )
                assert evaluator.eval(root) == expected, (
                    gap, matrix, mask, width)
                comparisons += 1
            cases.append({"gap": gap, "matrix_ref": matrix,
                          "parameter_slots": width - 2})

    wire_valid = wire_invalid = 0
    for length in range(14):
        for bits in map("".join, itertools.product("01", repeat=length)):
            try:
                matrices, actions = q.decode_bits(bits)
                assert q.encode_bits(matrices, actions) == bits
                wire_valid += 1
            except q.Invalid:
                wire_invalid += 1

    sample = [bin(n)[3:] for n in range(1, 256)]
    expected = [
        bits
        for length in range(8)
        for bits in map("".join, itertools.product("01", repeat=length))
    ]
    assert sample == expected

    return {
        "gap_parameter_epscs": len(cases),
        "independent_epsc_semantic_comparisons": comparisons,
        "wire_words_length_at_most_13": wire_valid + wire_invalid,
        "valid_wire_words": wire_valid,
        "invalid_wire_words": wire_invalid,
        "shortlex_prefix": len(sample),
        "status": "independent finite diagnostics only; no acceptance or consistency theorem",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    text = json.dumps(run(), indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
