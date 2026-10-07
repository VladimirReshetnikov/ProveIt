#!/usr/bin/env python3
"""Exact independent checks of the four-letter Boolean-relation compiler.

The checker interprets explicit transition tables. It does not use the
claimed matrix formula while simulating either the four-letter NFA or its
binary decoder. Integer path multiplicities, including initial-state
multiplicities, are retained. No third-party packages are required.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import time


class AuditError(RuntimeError):
    """A finite exact check disagreed with the specified semantics."""


LETTERS = ("a", "b", "t", "r")
BIT_CODES = {letter: (i // 2, i % 2) for i, letter in enumerate(LETTERS)}


def transition_tables(h: int):
    """State U_i is i and state V_i is h+i; missing transitions reject."""
    size = 2 * h
    table = {letter: [()] * size for letter in LETTERS}
    for i in range(h):
        table["a"][i] = ((i + 1) % h,)
        table["a"][h + i] = (h + i,)
        table["b"][i] = (i,)
        table["b"][h + i] = (h + (i + 1) % h,)
        table["t"][i] = (i, h) if i == 0 else (i,)
        table["t"][h + i] = (h + i,)
        table["r"][i] = ()
        table["r"][h + i] = (i,)

    # Three disjoint copies: complete bit-pair, first bit 0, first bit 1.
    binary = {bit: [()] * (3 * size) for bit in (0, 1)}
    for state in range(size):
        binary[0][state] = (size + state,)
        binary[1][state] = (2 * size + state,)
        for prefix in (0, 1):
            for bit in (0, 1):
                letter = LETTERS[2 * prefix + bit]
                binary[bit][(prefix + 1) * size + state] = table[letter][state]
    return table, binary


def relation_matrix(h: int, relation: int):
    return tuple(tuple((relation >> (i * h + j)) & 1 for j in range(h))
                 for i in range(h))


def word_for_relation(h: int, relation: int):
    word = []
    for i in range(h):
        for j in range(h):
            if relation & (1 << (((-i) % h) * h + ((-j) % h))):
                word.append("t")
            word.append("b")
        word.append("a")
    word.append("r")
    return tuple(word)


def binary_word(word):
    return tuple(bit for letter in word for bit in BIT_CODES[letter])


def run_exact(table, word, h: int):
    """Return all U-source to machine-state integer path counts.

    Pack the h distinct source coordinates into separated binary fields.
    Each state has at most two successors, so a field width len(word)+1
    strictly exceeds every possible coefficient; addition has no carry
    between source fields. This is exact integer linear propagation.
    """
    states = len(next(iter(table.values())))
    width = len(word) + 1
    mask = (1 << width) - 1
    dist = [0] * states
    for source in range(h):
        dist[source] = 1 << (width * source)
    for symbol in word:
        nxt = [0] * states
        transition = table[symbol]
        for state, weight in enumerate(dist):
            if weight:
                for target in transition[state]:
                    nxt[target] += weight
        dist = nxt
    return tuple(tuple((weight >> (width * source)) & mask for weight in dist)
                 for source in range(h))


def matrix_product(left, right):
    h = len(left)
    return tuple(tuple(sum(left[i][k] * right[k][j] for k in range(h))
                       for j in range(h)) for i in range(h))


def require_action(actual, expected, h: int, context):
    head = tuple(row[:h] for row in actual)
    tail = tuple(row[h:] for row in actual)
    if head != expected or any(any(row) for row in tail):
        raise AuditError(f"Incorrect canonical action: {context!r}; "
                         f"expected={expected!r}; actual={actual!r}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-order", type=int, default=4)
    parser.add_argument("--max-pair-order", type=int, default=3)
    parser.add_argument("--malformed-max-bits", type=int, default=12)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    if not 1 <= args.max_order <= 4:
        raise AuditError("The exhaustive preset requires 1 <= max-order <= 4.")
    if not 1 <= args.max_pair_order <= min(3, args.max_order):
        raise AuditError("max-pair-order must lie between 1 and min(3,max-order).")
    if not 0 <= args.malformed_max_bits <= 16:
        raise AuditError("malformed-max-bits must lie between 0 and 16.")

    started = time.monotonic()
    digest = hashlib.sha256()
    report = {"status": "passed", "arithmetic": "exact Python integers",
              "compiler": "2h four-letter states; 6h binary decoder states",
              "limits": vars(args).copy(), "checks": {}}
    report["limits"]["output"] = str(args.output)
    totals = {"single_relations": 0, "ordered_relation_pairs": 0,
              "singleton_contexts": 0, "arbitrary_binary_words": 0}
    cache = {}

    for h in range(1, args.max_order + 1):
        table, binary = transition_tables(h)
        records = []
        maximum_length = 0
        for relation in range(1 << (h * h)):
            expected = relation_matrix(h, relation)
            word = word_for_relation(h, relation)
            bits = binary_word(word)
            require_action(run_exact(table, word, h), expected, h,
                           ("four-letter", h, relation))
            require_action(run_exact(binary, bits, h), expected, h,
                           ("binary", h, relation))
            required_length = h * h + h + 1 + relation.bit_count()
            if len(word) != required_length or len(bits) != 2 * required_length:
                raise AuditError(f"Incorrect word length at h={h}, relation={relation}.")
            maximum_length = max(maximum_length, len(word))
            digest.update(f"single:{h}:{relation}:{''.join(word)}\n".encode())
            records.append((expected, word, bits))
            totals["single_relations"] += 1
        cache[h] = (table, binary, records)
        report["checks"][f"single_order_{h}"] = {
            "relations": len(records), "maximum_four_letter_word_length": maximum_length,
            "maximum_binary_word_length": 2 * maximum_length,
            "integer_path_counts": "exactly the matrix entries, without multiplicity"}
        print(f"single order {h}: {len(records)} relations passed", flush=True)

    for h in range(1, args.max_pair_order + 1):
        table, binary, records = cache[h]
        count = 0
        for left, (left_matrix, left_word, left_bits) in enumerate(records):
            for right, (right_matrix, right_word, right_bits) in enumerate(records):
                expected = matrix_product(left_matrix, right_matrix)
                require_action(run_exact(table, left_word + right_word, h), expected, h,
                               ("four-letter product", h, left, right))
                require_action(run_exact(binary, left_bits + right_bits, h), expected, h,
                               ("binary product", h, left, right))
                digest.update(f"pair:{h}:{left}:{right}:{expected!r}\n".encode())
                count += 1
        totals["ordered_relation_pairs"] += count
        report["checks"][f"pair_order_{h}"] = {
            "ordered_pairs": count,
            "integer_path_counts": "exact entries of the ordinary integer matrix product"}
        print(f"pair order {h}: {count} ordered pairs passed", flush=True)

        contexts = 0
        for relation, (matrix, word, bits) in enumerate(records):
            for i in range(h):
                for j in range(h):
                    prefix = records[1 << (i * h + i)]
                    suffix = records[1 << (j * h + j)]
                    expected = tuple(tuple(matrix[i][j] if (a, b) == (i, j) else 0
                                           for b in range(h)) for a in range(h))
                    require_action(run_exact(table, prefix[1] + word + suffix[1], h),
                                   expected, h, ("four-letter contexts", h, relation, i, j))
                    require_action(run_exact(binary, prefix[2] + bits + suffix[2], h),
                                   expected, h, ("binary contexts", h, relation, i, j))
                    digest.update(f"context:{h}:{relation}:{i}:{j}\n".encode())
                    contexts += 1
        totals["singleton_contexts"] += contexts
        report["checks"][f"contexts_order_{h}"] = {"relation_entry_contexts": contexts}
        print(f"context order {h}: {contexts} singleton contexts passed", flush=True)

    for h in range(1, args.max_order + 1):
        table, binary, _ = cache[h]
        count = 0
        for length in range(args.malformed_max_bits + 1):
            for bits in itertools.product((0, 1), repeat=length):
                actual = run_exact(binary, bits, h)
                decoded = tuple(LETTERS[2 * bits[i] + bits[i + 1]]
                                for i in range(0, length - 1, 2))
                direct = run_exact(table, decoded, h)
                if length % 2 == 0:
                    expected = tuple(tuple(row) + (0,) * (4 * h) for row in direct)
                else:
                    shift = (bits[-1] + 1) * 2 * h
                    expected = tuple((0,) * shift + tuple(row)
                                     + (0,) * (6 * h - shift - 2 * h) for row in direct)
                if actual != expected:
                    raise AuditError(f"Decoder disagreement on arbitrary bits h={h}, bits={bits!r}.")
                digest.update(f"bits:{h}:{''.join(map(str,bits))}\n".encode())
                count += 1
        totals["arbitrary_binary_words"] += count
        report["checks"][f"arbitrary_binary_order_{h}"] = {
            "words": count,
            "scope": "all binary strings up to the specified length, including odd lengths",
            "claim": "exact prefix-state behavior; no canonical-matrix promise was imposed"}
        print(f"arbitrary binary order {h}: {count} strings passed", flush=True)

    report["totals"] = totals
    report["total_test_cases"] = sum(totals.values())
    report["case_sha256"] = digest.hexdigest()
    report["elapsed_seconds"] = round(time.monotonic() - started, 3)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "passed", "totals": totals,
                      "case_sha256": report["case_sha256"],
                      "output": str(args.output),
                      "elapsed_seconds": report["elapsed_seconds"]}), flush=True)


if __name__ == "__main__":
    main()
