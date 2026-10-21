#!/usr/bin/env python3
"""Finite corroboration of the tag-lowering theorem; standard library only.

This program is not the all-natural proof. It checks exact parse/encode
inversion and every NIP-to-earlier-DROP image for a finite raw-code range.
Run with assertions enabled. No ProveIt source modules are imported.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path


def pair(a: int, b: int) -> int:
    assert a >= 0 and b >= 0
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    assert n >= 0
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    a = s - b
    assert pair(a, b) == n
    return a, b


def parse(n: int) -> tuple[tuple[int, ...], ...]:
    """Parse a raw candidate, preserving every command's complete fields."""
    assert n >= 0
    out = []
    while True:
        tag, residual = unpair(n)
        fields = [tag]
        extra = 0 if tag < 2 else (1 if tag == 2 else 2)
        for _ in range(extra):
            field, residual = unpair(residual)
            fields.append(field)
        out.append(tuple(fields))
        if residual == 0:
            return tuple(out)
        following = residual - 1
        assert following < n
        n = following


def encode(word: tuple[tuple[int, ...], ...]) -> int:
    """Raw first command, successor-coded nonempty continuations."""
    assert word
    continuation = 0
    for fields in reversed(word):
        assert fields and all(a >= 0 for a in fields)
        tag = fields[0]
        assert len(fields) == (1 if tag < 2 else (2 if tag == 2 else 3))
        raw = continuation
        for field in reversed(fields):
            raw = pair(field, raw)
        continuation = raw + 1
    return continuation - 1


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=5000)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    assert args.limit >= 6

    # Explicitly exercise raw zero and zero-valued final commands after
    # each command arity. Their predecessors must use positive residual 1.
    boundary_words = [
        ((0,),),
        ((1,),),
        ((0,), (0,)),
        ((1,), (0,)),
        ((2, 0), (0,)),
        ((3, 0, 0), (0,)),
        ((0,), (1,), (0,)),
        ((3, 7, 9), (2, 11), (1,), (0,)),
    ]
    assert pair(0, 0) == 0 and encode(((0,),)) == 0
    boundaries = []
    for word in boundary_words:
        raw = encode(word)
        assert parse(raw) == word
        boundaries.append({'word': word, 'raw': raw})

    images: set[tuple[int, int]] = set()
    drop_count = nip_count = prefix_balance = 0
    min_balance = 0
    max_length = 0
    examples = []
    for n in range(args.limit):
        word = parse(n)
        assert encode(word) == n
        max_length = max(max_length, len(word))
        for j, fields in enumerate(word):
            if fields[0] == 0:
                drop_count += 1
                prefix_balance += 1
            elif fields[0] == 1:
                lowered = word[:j] + ((0,),) + word[j + 1:]
                m = encode(lowered)
                assert m < n
                assert parse(m) == lowered
                image = (m, j)
                assert image not in images
                images.add(image)
                # Construct the inverse, not just a set-cardinality check.
                recovered = lowered[:j] + ((1,),) + lowered[j + 1:]
                assert encode(recovered) == n
                nip_count += 1
                prefix_balance -= 1
                if len(examples) < 12:
                    examples.append({'nip': [n, j], 'drop_image': [m, j]})
            # MP and AX are both assigned zero conservative balance.
            min_balance = min(min_balance, prefix_balance)
            assert prefix_balance >= 0
    assert len(images) == nip_count
    assert prefix_balance == drop_count - nip_count

    receipt = {
        'status': 'FINITE_TAG_LOWERING_CORROBORATION_PASS',
        'scope': 'Finite exact corroboration only; the all-natural result is the separate tag-lowering injection proof.',
        'candidate_range': [0, args.limit],
        'range_endpoint_exclusive': True,
        'parse_encode_identities_checked': args.limit,
        'NIP_occurrences_and_distinct_earlier_DROP_images': nip_count,
        'DROP_occurrences': drop_count,
        'AX_balance_assumed': 0,
        'MP_balance_assumed': 0,
        'minimum_command_prefix_balance': min_balance,
        'final_balance': prefix_balance,
        'maximum_commands_per_candidate': max_length,
        'boundary_examples': boundaries,
        'tag_lowering_examples': examples,
        'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.out.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled.')
    main()
