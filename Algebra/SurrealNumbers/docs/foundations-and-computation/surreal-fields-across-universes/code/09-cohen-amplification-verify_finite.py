#!/usr/bin/env python3
"""Finite checks for Full Gap Spectra of Old Surreal Fields.

These tests check finite sign and block-code formulas only. They cannot test
freshness, genericity, forcing preservation, cofinalities, or class arguments.
Python 3.9+; no third-party dependencies.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from typing import Iterable, Sequence

Sign = tuple[int, ...]  # -1 is minus; +1 is plus; termination compares as zero.


def signs_through(length: int) -> list[Sign]:
    if length < 0:
        raise ValueError("The maximum length must be nonnegative.")
    return [s for n in range(length + 1)
            for s in itertools.product((-1, 1), repeat=n)]


def compare(left: Sign, right: Sign) -> int:
    """Lexicographic comparison with -1 < termination < +1."""
    for position in range(max(len(left), len(right))):
        a = left[position] if position < len(left) else 0
        b = right[position] if position < len(right) else 0
        if a != b:
            return (a > b) - (a < b)
    return 0


def canonical_options(sign: Sign) -> tuple[list[Sign], list[Sign]]:
    left = [sign[:i] for i, bit in enumerate(sign) if bit == 1]
    right = [sign[:i] for i, bit in enumerate(sign) if bit == -1]
    return left, right


def encode(values: Sequence[int], width: int) -> Sign:
    """Put exactly one plus in each fixed-width block."""
    if width < 2:
        raise ValueError("A block must have space for a plus and a minus.")
    if any(not 0 <= value < width - 1 for value in values):
        raise ValueError("Values must leave at least one spare block position.")
    return tuple(1 if position == value else -1
                 for value in values for position in range(width))


def decode(sign: Sign, width: int) -> tuple[int, ...]:
    if width < 2 or len(sign) % width:
        raise ValueError("The sign must consist of whole valid blocks.")
    values = []
    for start in range(0, len(sign), width):
        block = sign[start:start + width]
        if block.count(1) != 1 or block[-1] != -1:
            raise ValueError("A valid block has one plus and a spare final minus.")
        values.append(block.index(1))
    return tuple(values)


def pushforward(labels: Iterable[str], images: dict[str, str]) -> list[str]:
    """Finite set-image bookkeeping; the supplied cofinality labels are inputs."""
    return sorted({images[label] for label in labels})


def run_checks() -> dict[str, object]:
    # Test against a deeper ambient tree, including all possible extensions.
    source_signs = signs_through(7)
    ambient_signs = signs_through(9)
    cone_cases = 0
    comparison_cases = 0
    for sign in source_signs:
        left, right = canonical_options(sign)
        assert all(compare(a, sign) < 0 for a in left)
        assert all(compare(sign, b) < 0 for b in right)
        for candidate in ambient_signs:
            separator = (all(compare(a, candidate) < 0 for a in left)
                         and all(compare(candidate, b) < 0 for b in right))
            extension = (len(candidate) >= len(sign)
                         and candidate[:len(sign)] == sign)
            assert separator == extension, (sign, candidate)
            assert compare(sign, candidate) == -compare(candidate, sign)
            cone_cases += 1
            comparison_cases += 1

    code_cases = 0
    prefix_cases = 0
    for alphabet_size in range(1, 6):
        width = alphabet_size + 2
        for length in range(6):
            for values in itertools.product(range(alphabet_size), repeat=length):
                sign = encode(values, width)
                assert decode(sign, width) == values
                assert sign.count(1) == length
                assert len(sign) == width * length
                code_cases += 1
                for endpoint in range(len(sign) + 1):
                    # A prefix ending inside a block needs that block's value;
                    # a boundary prefix needs only the previous blocks.
                    required = (endpoint + width - 1) // width
                    assert encode(values[:required], width)[:endpoint] == sign[:endpoint]
                    prefix_cases += 1

    examples = {
        "Prikry": pushforward(["omega", "rho"],
                              {"omega": "omega", "rho": "omega"}),
        "Namba_under_CH": pushforward(
            ["omega", "omega1_M", "omega2_M"],
            {"omega": "omega", "omega1_M": "omega1_N", "omega2_M": "omega"}),
        "finite_Easton": pushforward(["aleph1", "aleph3"],
                                     {"aleph1": "aleph1", "aleph3": "aleph3"}),
    }
    assert examples["Prikry"] == ["omega"]
    assert set(examples["Namba_under_CH"]) == {"omega", "omega1_N"}
    assert examples["finite_Easton"] == ["aleph1", "aleph3"]

    return {
        "status": "PASS",
        "scope": "Finite indexing and sign-order checks only; no transfinite verification.",
        "canonical_cone_cases": cone_cases,
        "comparison_antisymmetry_cases": comparison_cases,
        "block_encode_decode_cases": code_cases,
        "block_prefix_cases": prefix_cases,
        "symbolic_image_examples": examples,
        "excluded_claims": ["freshness", "forcing", "cardinality preservation",
                            "actual cofinality calculations", "saturation", "class recursion"],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="Optional JSON output path; existing output is replaced.")
    args = parser.parse_args()
    result = run_checks()
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
