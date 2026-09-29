#!/usr/bin/env python3
"""Finite checks for the coarse-information profile construction.

These checks verify finite algebra and counting identities, not the infinite
computability theorems, genericity, cone-avoiding compactness, or novelty.
Python 3.10+, standard library only. Run from any working directory.
"""
from __future__ import annotations

from collections import Counter
from itertools import product
from pathlib import Path
import json
import random


def members(mask: int, n: int) -> list[int]:
    return [i for i in range(n) if mask & (1 << i)]


def rank(rows: list[int]) -> int:
    """Rank over F_2 of bit-packed rows, by exact Gaussian elimination."""
    pivots: dict[int, int] = {}
    for row in rows:
        while row:
            p = row.bit_length() - 1
            if p in pivots:
                row ^= pivots[p]
            else:
                pivots[p] = row
                break
    return len(pivots)


def xor_all(values: list[int] | tuple[int, ...]) -> int:
    answer = 0
    for value in values:
        answer ^= value
    return answer


def sharing_checks() -> dict[str, int]:
    distributions = reconstructions = 0
    for r in range(1, 9):
        for secret in (0, 1):
            for pads in product((0, 1), repeat=r - 1):
                shares = (*pads, secret ^ xor_all(pads))
                assert xor_all(shares) == secret
                reconstructions += 1
        for obs in range((1 << r) - 1):
            ix = members(obs, r)
            tables = []
            for secret in (0, 1):
                table: Counter[tuple[int, ...]] = Counter()
                for pads in product((0, 1), repeat=r - 1):
                    shares = (*pads, secret ^ xor_all(pads))
                    table[tuple(shares[j] for j in ix)] += 1
                tables.append(table)
            assert tables[0] == tables[1]
            assert len(tables[0]) == (1 << len(ix))
            assert len(set(tables[0].values())) == 1
            distributions += 1
    return {"all_of_r_max_r": 8, "reconstruction_cases": reconstructions,
            "proper_observation_distributions": distributions}


def profile_rank_checks() -> dict[str, int]:
    coalitions = 0
    for n in range(1, 8):
        # Every party first receives a distinct private mask coordinate.
        next_mask = n
        rows_by_party: list[list[tuple[int, int]]] = [[(1 << i, 0)] for i in range(n)]
        for s in range(1, 1 << n):
            people = members(s, n)
            pad_rows = []
            for i in people[:-1]:
                row = 1 << next_mask
                next_mask += 1
                pad_rows.append(row)
                rows_by_party[i].append((row, 0))
            rows_by_party[people[-1]].append((xor_all(pad_rows), 1 << (s - 1)))
        width = (1 << (n - 1)) + 1
        assert all(len(rows) == width for rows in rows_by_party)
        for c in range(1, 1 << n):
            people = members(c, n)
            selected = [row for i in people for row in rows_by_party[i]]
            auth = (1 << len(people)) - 1
            expected = len(people) * width - auth
            assert rank([mask for mask, _ in selected]) == expected
            # Each fully observed component adds its own independent parity relation.
            assert rank([mask | (secret << next_mask) for mask, secret in selected]) == len(selected)
            coalitions += 1
    return {"max_participants": 7, "coalitions_checked": coalitions}


def normal_form_checks() -> dict[str, int]:
    rng = random.Random(20260928)
    checked = 0
    for n in range(1, 7):
        for c in range(1, 1 << n):
            for s in range(1, 1 << n):
                people = members(s, n)
                visible = [j for j, i in enumerate(people) if c & (1 << i)]
                if not visible:
                    continue
                for _ in range(16):
                    secret = rng.randrange(2)
                    pads = [rng.randrange(2) for _ in people[:-1]]
                    shares = [*pads, secret ^ xor_all(pads)]
                    if len(visible) == len(people):
                        regenerated = [*pads, secret ^ xor_all(pads)]
                        assert regenerated == shares
                    elif len(people) - 1 in visible:
                        missing = next(j for j in range(len(pads)) if j not in visible)
                        transformed = pads.copy()
                        transformed[missing] = shares[-1]
                        inverse = transformed.copy()
                        inverse[missing] = secret ^ transformed[missing] ^ xor_all(
                            [transformed[j] for j in range(len(pads)) if j != missing])
                        assert inverse == pads
                        for j in visible:
                            got = transformed[missing] if j == len(people) - 1 else transformed[j]
                            assert got == shares[j]
                    else:
                        assert all(shares[j] == pads[j] for j in visible)
                    checked += 1
    return {"max_participants": 6, "normal_form_cases": checked, "seed": 20260928}


def density_checks() -> dict[str, int]:
    tail_checks = column_checks = xor_checks = 0
    for N in range(2049):
        for m in range(11):
            count = sum((k + 1) % (1 << m) == 0 for k in range(N))
            assert count == N // (1 << m)
            tail_checks += 1
    for x in range(50000):
        k = ((x + 1) & -(x + 1)).bit_length() - 1
        t = ((x + 1) // (1 << k) - 1) // 2
        assert (1 << k) * (2 * t + 1) - 1 == x
        column_checks += 1
    for r in range(1, 7):
        for a in product((0, 1), repeat=r):
            for b in product((0, 1), repeat=r):
                assert (xor_all(a) != xor_all(b)) <= any(x != y for x, y in zip(a, b))
                xor_checks += 1
    return {"dyadic_tail_checks": tail_checks, "column_inverse_checks": column_checks,
            "xor_error_inclusion_checks": xor_checks}


def majority_checks() -> dict[str, int]:
    cases = 0
    for length in (1, 2, 4, 8, 16):
        for bits in range(1 << length):
            ones = bits.bit_count()
            majority = int(2 * ones > length)  # Tie goes to zero.
            for secret in (0, 1):
                errors = ones if secret == 0 else length - ones
                if 2 * errors < length:
                    assert majority == secret
                if majority != secret:
                    assert 2 * errors >= length
                cases += 1
    return {"maximum_block_length": 16, "majority_cases": cases}


def access_checks() -> dict[str, int]:
    count = 0
    n = 4
    for family in range(1 << (1 << n)):
        if family & 1:  # The empty coalition is not authorized.
            continue
        authorized = {c for c in range(1 << n) if family & (1 << c)}
        if any((c | (1 << i)) not in authorized for c in authorized for i in range(n)):
            continue
        minimal = {c for c in authorized if not any(d != c and d & c == d for d in authorized)}
        rebuilt = {c for c in range(1 << n) if any(d & c == d for d in minimal)}
        assert rebuilt == authorized
        count += 1
    assert count == 167  # Includes the empty authorization family.
    return {"participants": n, "monotone_access_families": count}


def main() -> None:
    output = {
        "status": "all finite checks passed",
        "scope": "Finite algebra/counting only; not an infinite or machine-checked proof.",
        "sharing": sharing_checks(),
        "profile_rank": profile_rank_checks(),
        "normal_form": normal_form_checks(),
        "density": density_checks(),
        "majority": majority_checks(),
        "access": access_checks(),
    }
    text = json.dumps(output, indent=2) + "\n"
    (Path(__file__).resolve().parent / "results.json").write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
