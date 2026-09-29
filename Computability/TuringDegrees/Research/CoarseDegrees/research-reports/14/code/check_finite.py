#!/usr/bin/env python3
"""Deterministic finite checks for the companion mathematical article.

These tests do NOT establish genericity, computable agreement, the truth of an
infinite density limit, or the nonexistence of least Turing degrees. They check
finite coordinate identities, finite search invariants, and counting formulas.
Python 3.10+; standard library only. Results are written next to this script.
"""
from __future__ import annotations

from bisect import bisect_left
from fractions import Fraction
from math import isqrt
from pathlib import Path
from random import Random
from typing import Callable
import json

Order = Callable[[int], int]


def erase(bits: int, mask: int, length: int) -> int:
    """Zero masked coordinates of a finite bit string."""
    return bits & (~mask) & ((1 << length) - 1)


def description_checks(max_length: int = 6) -> dict[str, int]:
    cases = 0
    for length in range(max_length + 1):
        full = (1 << length) - 1
        for x in range(1 << length):
            for mask in range(1 << length):
                y = erase(x, mask, length)
                for omissions in range(1 << length):
                    d = tuple(None if omissions >> n & 1 else x >> n & 1
                              for n in range(length))
                    e = tuple(None if omissions >> n & 1 else y >> n & 1
                              for n in range(length))
                    forward = tuple(0 if mask >> n & 1 else d[n]
                                    for n in range(length))
                    backward = tuple(None if mask >> n & 1 else e[n]
                                     for n in range(length))
                    assert all(v is None or v == (y >> n & 1)
                               for n, v in enumerate(forward))
                    assert all(v is None or v == (x >> n & 1)
                               for n, v in enumerate(backward))
                    sf = sum(1 << n for n, v in enumerate(forward)
                             if v is None)
                    sb = sum(1 << n for n, v in enumerate(backward)
                             if v is None)
                    assert sf == omissions & (~mask) & full
                    assert sb == (omissions | mask) & full
                    cases += 1
    return {"maximum_length": max_length, "description_mask_instances": cases}


def independence_checks(max_length: int = 8) -> dict[str, int]:
    erased_flips = visible_flips = 0
    for length in range(1, max_length + 1):
        for x in range(1 << length):
            for mask in range(1 << length):
                y = erase(x, mask, length)
                for n in range(length):
                    changed = erase(x ^ (1 << n), mask, length)
                    if mask >> n & 1:
                        assert changed == y
                        erased_flips += 1
                    else:
                        assert changed == y ^ (1 << n)
                        visible_flips += 1
    return {"maximum_length": max_length, "erased_bit_flips": erased_flips,
            "retained_bit_flips": visible_flips}


def join_and_amalgamation_checks() -> dict[str, int]:
    join_cases = 0
    for length in range(6):
        full = (1 << length) - 1
        for x in range(1 << length):
            for c in range(1 << length):
                for d in range(1 << length):
                    xc, xd = erase(x, c, length), erase(x, d, length)
                    # Use X_C off C and X_D on C\D, zero on C intersection D.
                    recovered = (xc | (xd & c)) & full
                    assert recovered == erase(x, c & d, length)
                    assert erase(recovered, c, length) == xc
                    assert erase(recovered, d, length) == xd
                    join_cases += 1
    compatible_cases = 0
    for length in range(5):
        full = (1 << length) - 1
        for c in range(1 << length):
            for d in range(1 << length):
                shared = (~(c | d)) & full
                psi_private = c & (~d) & full
                for tau in range(1 << length):
                    for eta in range(1 << length):
                        if (tau ^ eta) & shared:
                            continue
                        nu = ((tau & ~psi_private) | (eta & psi_private)) & full
                        assert erase(nu, c, length) == erase(tau, c, length)
                        assert erase(nu, d, length) == erase(eta, d, length)
                        # Any fixed prefix on which tau and eta agree survives.
                        assert ((nu ^ tau) & (~(tau ^ eta)) & full) == 0
                        compatible_cases += 1
    return {"join_instances": join_cases,
            "compatible_amalgamation_instances": compatible_cases}


def checked_budget(budget: Order, n: int) -> int:
    value = budget(n)
    if not isinstance(value, int) or value < 0:
        raise ValueError("A budget must return a nonnegative integer.")
    return value


def find_endpoint(budget: Order, lower: int, quota: int) -> int:
    """Find the least m >= lower with b(m) >= quota for a known monotone order.

    Doubling plus binary search avoids iterating across enormous empty gaps.
    The test script uses only the explicitly defined unbounded orders below.
    The expansion guard prevents accidental endless use with a bad input.
    """
    if checked_budget(budget, lower) >= quota:
        return lower
    lo, hi = lower, max(2, lower * 2)
    for _ in range(256):
        if checked_budget(budget, hi) >= quota:
            break
        lo, hi = hi, hi * 2
    else:
        raise RuntimeError("Budget threshold not reached in the test guard.")
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if checked_budget(budget, mid) >= quota:
            hi = mid
        else:
            lo = mid
    return hi


def blocks(budget: Order, capacities: list[int]) -> list[int]:
    endpoints: list[int] = []
    quota = 0
    for n, capacity in enumerate(capacities):
        if capacity <= 0:
            raise ValueError("Capacities must be positive.")
        quota += capacity
        lower = max(4 ** (n + 1), 2 * n + 3, (n + 1) * quota,
                    4 * endpoints[-1] if endpoints else 1)
        m = find_endpoint(budget, lower, quota)
        assert m >= (n + 1) * quota
        assert checked_budget(budget, m) >= quota
        endpoints.append(m)
    return endpoints


def all_prefix_budget_for_finite_set(points: set[int], budget: Order) -> int:
    """Check all count-change positions; monotonicity covers each full plateau.

    This certifies the budget of this FINITE set at every natural prefix,
    not a limit construction or the totality of an unknown function.
    """
    ordered = sorted(points)
    probes = {0} | {p + 1 for p in ordered}
    for n in probes:
        assert bisect_left(ordered, n) <= checked_budget(budget, n)
    return len(probes)


def packed_mask_checks() -> dict[str, object]:
    orders: dict[str, Order] = {
        "linear": lambda n: n,
        "integer_square_root": isqrt,
        "floor_log2_n_plus_1": lambda n: (n + 1).bit_length() - 1,
    }
    # Duplicate functions deliberately stress the fresh-offset requirement.
    functions: list[Order] = [lambda n: 0, lambda n: 0, lambda n: n,
                             lambda n: n * n, lambda n: 2 ** n,
                             lambda n: n + 1, lambda n: n // 2,
                             lambda n: n * (n + 1) // 2,
                             lambda n: 17, lambda n: 3 * n + 7,
                             lambda n: 2 ** (n + 5), lambda n: n ** 3]
    capacities = [2 * (n + 1) for n in range(12)]
    records: dict[str, object] = {}
    for name, budget in orders.items():
        starts = blocks(budget, capacities)
        masks: list[set[int]] = [set() for _ in functions]
        fresh = 0
        for n, m in enumerate(starts):
            used: set[int] = set()
            for i in range(min(n + 1, len(functions))):
                p = functions[i](n) % m
                q = 0
                while q in used or q == p:
                    q += 1
                assert q < m and q not in used and q != p
                before = set(used)
                used.update((p, q))
                assert q not in before
                fresh += 1
                for j in range(i, len(masks)):
                    masks[j].update((m + p, m + q))
            assert len(used) <= capacities[n]
        prefix_probes = 0
        union = set().union(*masks)
        for i, mask in enumerate(masks):
            prefix_probes += all_prefix_budget_for_finite_set(mask, budget)
            if i:
                assert masks[i - 1] < mask
        prefix_probes += all_prefix_budget_for_finite_set(union, budget)
        for n, m in enumerate(starts):
            quota = (n + 1) * (n + 2)
            assert len([p for p in union if p < 2 * m]) <= quota
            assert Fraction(quota, m) <= Fraction(1, n + 1)
        records[name] = {
            "block_count": len(starts), "mask_count": len(masks),
            "fresh_insertions": fresh, "prefix_plateau_probes": prefix_probes,
            "maximum_endpoint_bit_length": max(starts).bit_length(),
            "union_size": len(union),
        }
    return records


def choice_checks(max_size: int = 9) -> dict[str, int]:
    cases = 0
    for size in range(1, max_size + 1):
        for subset in range(1 << size):
            outside = [k for k in range(size) if not (subset >> k & 1)]
            choice = outside[0] if outside else 0
            for h in range(2 * size + 3):
                selected = h % size
                if outside and h == choice:
                    assert not (subset >> selected & 1)
                if outside and (subset >> selected & 1):
                    assert h != choice
                cases += 1
    return {"maximum_block_size": max_size, "choice_instances": cases}


def p_ideal_checks(seed: int = 20260928) -> dict[str, int]:
    rng = Random(seed)
    finite_row_cases = 0
    max_n, row_count = 7, 8
    for _ in range(200):
        rows = [{p for p in range(1 << (max_n + 1)) if rng.randrange(7) == 0}
                for _ in range(row_count)]
        result: set[int] = set()
        for n in range(max_n + 1):
            start, end = 1 << n, 1 << (n + 1)
            candidates = [0]
            unions: dict[int, set[int]] = {0: set()}
            running: set[int] = set()
            for k in range(1, n + 2):
                running |= rows[k - 1]
                unions[k] = {p for p in running if start <= p < end}
                if len(unions[k]) * k <= start:
                    candidates.append(k)
            chosen = max(candidates)
            block_output = unions[chosen]
            if chosen:
                assert len(block_output) * chosen <= start
                for i in range(chosen):
                    assert {p for p in rows[i] if start <= p < end} <= block_output
            else:
                assert not block_output
            result |= block_output
            finite_row_cases += 1
        assert 0 not in result
    inequality_cases = 0
    for epsilon in [Fraction(0), Fraction(1, 8), Fraction(1, 4),
                    Fraction(1, 2), Fraction(1)]:
        for n0 in range(5):
            for _ in range(20):
                s = {p for p in range(1 << n0) if rng.randrange(2)}
                for n in range(n0, 6):
                    block = list(range(1 << n, 1 << (n + 1)))
                    quota = int(epsilon * len(block))
                    s.update(rng.sample(block, rng.randrange(quota + 1)))
                for n in range(n0, 6):
                    for prefix in range(1 << n, 1 << (n + 1)):
                        count = sum(p < prefix for p in s)
                        assert count <= (1 << n0) + epsilon * (1 << (n + 1))
                        inequality_cases += 1
    return {"seed": seed, "finite_row_selection_cases": finite_row_cases,
            "partial_block_inequalities": inequality_cases}


def main() -> None:
    result = {
        "status": "all finite checks passed",
        "scope": "Finite invariants only; not a proof of the infinite theorems.",
        "description_transformations": description_checks(),
        "erasure_independence": independence_checks(),
        "join_and_amalgamation": join_and_amalgamation_checks(),
        "bounded_choice": choice_checks(),
        "packed_masks": packed_mask_checks(),
        "uniform_null_upper_bound": p_ideal_checks(),
    }
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    folder = Path(__file__).resolve().parent
    (folder / "results.json").write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
