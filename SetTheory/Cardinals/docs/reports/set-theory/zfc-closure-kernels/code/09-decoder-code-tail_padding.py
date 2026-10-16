#!/usr/bin/env python3
"""Exact arithmetic checks for the cofinal START padding lemma.

This file uses Python integers, never fingerprints.  It checks the command
encoding identities on a finite grid; the universal theorem is proved in
the article.  It does not search for a refutation of ZFC.
"""
from __future__ import annotations

import argparse
import json
from math import isqrt
from pathlib import Path


def pair(a: int, b: int) -> int:
    if min(a, b) < 0:
        raise ValueError("natural numbers required")
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    if n < 0:
        raise ValueError("natural number required")
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def encode_fields(fields: tuple[int, ...], tail: int) -> int:
    for field in reversed(fields):
        tail = pair(field, tail)
    return tail


def encode_tail(commands: list[tuple[int, ...]]) -> int:
    tail = 0
    for command in reversed(commands):
        tail = 1 + encode_fields(command, tail)
    return tail


def start_candidate(padding: int, continuation: int) -> int:
    # First command has no outer successor: AX(c=0,x=1,y=1,u=padding).
    return encode_fields((3, 1, 1, padding), continuation)


def decode_four(n: int) -> tuple[tuple[int, ...], int]:
    fields = []
    for _ in range(4):
        field, n = unpair(n)
        fields.append(field)
    return tuple(fields), n


def run_checks() -> dict:
    inverse_pairs = 0
    for a in range(128):
        for b in range(128):
            n = pair(a, b)
            assert unpair(n) == (a, b)
            assert n >= max(a, b)
            inverse_pairs += 1
    for n in range(32768):
        assert pair(*unpair(n)) == n

    padding_cases = 0
    max_bits = 0
    for continuation in range(256):
        last = -1
        for padding in range(128):
            n = start_candidate(padding, continuation)
            fields, tail = decode_four(n)
            assert fields == (3, 1, 1, padding)
            assert tail == continuation
            assert n >= padding and n > last
            last = n
            max_bits = max(max_bits, n.bit_length())
            padding_cases += 1

    # The standard three-command halt suffix.  This only checks its integer
    # encoding and first-command decoding; no false theorem is supplied.
    suffix = [(1, 0), (2, 0), (2, 0)]
    continuation = encode_tail(suffix)
    suffix_cases = []
    for cutoff in (0, 1, 2, 100, 10**6, 10**30, 10**100):
        padding = cutoff + 1
        n = start_candidate(padding, continuation)
        fields, tail = decode_four(n)
        assert fields == (3, 1, 1, padding) and tail == continuation
        assert n > cutoff
        suffix_cases.append({"cutoff_digits": len(str(cutoff)),
                             "candidate_bits": n.bit_length(),
                             "above_cutoff": True})
    return {
        "status": "PASS",
        "arithmetic": "exact unbounded Python integers; no probabilistic equality",
        "pair_inverse_pairs": inverse_pairs,
        "inverse_naturals": 32768,
        "padding_cases": padding_cases,
        "largest_grid_candidate_bits": max_bits,
        "suffix_examples": suffix_cases,
        "scope": "Finite regression for universal arithmetic identities proved in the article; neither a ZFC refutation nor a new blank-tape machine.",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run_checks()
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O: this regression relies on assertions.")
    main()
