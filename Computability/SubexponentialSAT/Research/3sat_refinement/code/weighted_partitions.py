#!/usr/bin/env python3
"""Exact ranking of weighted exponent tuples and a mode-sum identity check.

This standard-library prototype validates mode-index compression only.  It
does not provide the low-degree local factorization needed to turn compressed
mode indices into a faster SAT or tensor-contraction algorithm.

For positive integer weights w_0,...,w_{q-1}, the exact fiber at total b is
{beta in N^q: sum(w_i beta_i)=b}.  Tuples are ordered lexicographically.
For a strict budget P, fibers are ordered first by total b=0,...,P-1 and
then lexicographically.  The dynamic program uses O(q B) integer cells/time
through a supplied maximum total B; this is pseudopolynomial in numeric B.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import time


class WeightedTuples:
    """Rank/unrank weighted nonnegative exponent tuples with exact arithmetic."""

    def __init__(self, weights, max_total):
        self.weights = tuple(weights)
        if any(not isinstance(w, int) or w <= 0 for w in self.weights):
            raise ValueError("All mode weights must be positive integers")
        if not isinstance(max_total, int) or max_total < 0:
            raise ValueError("Maximum total must be a nonnegative integer")
        self.max_total = max_total
        q = len(self.weights)
        # suffix[i][b] counts tuples on modes i,...,q-1 of exact weight b.
        self.suffix = [[0] * (max_total + 1) for _ in range(q + 1)]
        self.suffix[q][0] = 1
        for i in range(q - 1, -1, -1):
            weight = self.weights[i]
            for b in range(max_total + 1):
                self.suffix[i][b] = self.suffix[i + 1][b]
                if b >= weight:
                    self.suffix[i][b] += self.suffix[i][b - weight]
        self.prefix = [0]
        for count in self.suffix[0]:
            self.prefix.append(self.prefix[-1] + count)

    def _total(self, b):
        if not isinstance(b, int) or not 0 <= b <= self.max_total:
            raise ValueError("Total is outside the constructed table")

    def _budget(self, strict_budget):
        if not isinstance(strict_budget, int) or not 0 <= strict_budget <= self.max_total + 1:
            raise ValueError("Strict budget is outside the constructed table")

    def weighted_total(self, beta):
        beta = tuple(beta)
        if len(beta) != len(self.weights):
            raise ValueError("Wrong number of exponents")
        if any(not isinstance(x, int) or x < 0 for x in beta):
            raise ValueError("Exponents must be nonnegative integers")
        return sum(w * x for w, x in zip(self.weights, beta))

    def count_exact(self, b):
        self._total(b)
        return self.suffix[0][b]

    def count_below(self, strict_budget):
        self._budget(strict_budget)
        return self.prefix[strict_budget]

    def bits_exact(self, b):
        """Minimum fixed binary width for a nonempty exact fiber."""
        count = self.count_exact(b)
        if count == 0:
            raise ValueError("An empty fiber has no valid rank code")
        return (count - 1).bit_length()

    def rank_exact(self, b, beta):
        self._total(b)
        beta = tuple(beta)
        if self.weighted_total(beta) != b:
            raise ValueError("Tuple has the wrong exact total")
        rank = 0
        remaining = b
        for i, (weight, chosen) in enumerate(zip(self.weights, beta)):
            # All smaller first exponents precede the chosen block.
            for candidate in range(chosen):
                rank += self.suffix[i + 1][remaining - weight * candidate]
            remaining -= weight * chosen
        assert remaining == 0
        return rank

    def unrank_exact(self, b, rank):
        self._total(b)
        if not isinstance(rank, int) or not 0 <= rank < self.count_exact(b):
            raise ValueError("Rank is outside this exact fiber")
        remaining = b
        beta = []
        for i, weight in enumerate(self.weights):
            for candidate in range(remaining // weight + 1):
                block = self.suffix[i + 1][remaining - weight * candidate]
                if rank < block:
                    beta.append(candidate)
                    remaining -= weight * candidate
                    break
                rank -= block
            else:
                raise AssertionError("Dynamic-program rank decomposition failed")
        assert remaining == 0 and rank == 0
        return tuple(beta)

    def rank_below(self, strict_budget, beta):
        self._budget(strict_budget)
        beta = tuple(beta)
        total = self.weighted_total(beta)
        if total >= strict_budget:
            raise ValueError("Tuple does not satisfy the strict budget")
        return self.prefix[total] + self.rank_exact(total, beta)

    def unrank_below(self, strict_budget, rank):
        self._budget(strict_budget)
        if not isinstance(rank, int) or not 0 <= rank < self.count_below(strict_budget):
            raise ValueError("Rank is outside this cumulative budget")
        for total in range(strict_budget):
            count = self.count_exact(total)
            if rank < count:
                return self.unrank_exact(total, rank)
            rank -= count
        raise AssertionError("Cumulative rank decomposition failed")


def brute_tuples_below(weights, strict_budget):
    """Independent finite Cartesian enumeration used only for tiny checks."""
    if strict_budget <= 0:
        return []
    ranges = [range((strict_budget - 1) // w + 1) for w in weights]
    return [beta for beta in itertools.product(*ranges)
            if sum(w * x for w, x in zip(weights, beta)) < strict_budget]


def budget_arrays(number, strict_budget):
    """Yield all nonnegative arrays b_1,...,b_number with sum b_i<P."""
    if strict_budget <= 0:
        return
    if number == 0:
        yield ()
        return
    for first in range(strict_budget):
        for rest in budget_arrays(number - 1, strict_budget - first):
            yield (first,) + rest


# Distinct modes of equal weight are still separate coordinates.  Both
# directions are present; pair order and each pair's mode order are fixed.
DIRECTED_PAIRS = (
    ((0, 1), (1, 3)),
    ((1, 0), (2,)),
    ((0, 2), (1, 2)),
    ((2, 0), (2,)),
    ((1, 2), (1, 3)),
    ((2, 1), (1,)),
)


def split_by_pair(beta):
    result = []
    offset = 0
    for _, weights in DIRECTED_PAIRS:
        result.append(tuple(beta[offset:offset + len(weights)]))
        offset += len(weights)
    assert offset == len(beta)
    return tuple(result)


def toy_group_function(group, tuple_by_pair, modulus):
    """A deterministic modular function using only modes incident to group.

    Squared and mixed terms ensure the check is not just a separable product
    of one-mode geometric sums.  Nonincident tuples are never inspected.
    """
    incident = []
    for pair_index, ((source, target), _) in enumerate(DIRECTED_PAIRS):
        if group not in (source, target):
            continue
        role = 1 if group == source else 2
        for mode_index, exponent in enumerate(tuple_by_pair[pair_index]):
            incident.append((pair_index, mode_index, role, exponent))
    value = 11 + 13 * group
    for pair_index, mode_index, role, exponent in incident:
        value += (pair_index + 1) * (mode_index + 2) * (role + 1) * (exponent + 1)**2
    for left, right in zip(incident, incident[1:]):
        value += (group + 3) * (left[3] + 1) * (right[3] + 2)
    return value % modulus


def toy_product(tuple_by_pair, modulus):
    result = 1
    for group in range(3):
        result = result * toy_group_function(group, tuple_by_pair, modulus) % modulus
    return result


def check_three_group_identity(strict_budget, modulus):
    flat_weights = tuple(w for _, weights in DIRECTED_PAIRS for w in weights)
    direct_tuples = brute_tuples_below(flat_weights, strict_budget)
    direct_sum = sum(toy_product(split_by_pair(beta), modulus)
                     for beta in direct_tuples) % modulus

    tables = [WeightedTuples(weights, strict_budget - 1)
              for _, weights in DIRECTED_PAIRS]
    encoded_sum = 0
    valid_words = 0
    invalid_words = 0
    arrays = 0
    empty_fiber_arrays = 0
    recovered = set()
    for allocations in budget_arrays(len(DIRECTED_PAIRS), strict_budget):
        arrays += 1
        counts = [table.count_exact(b) for table, b in zip(tables, allocations)]
        if any(count == 0 for count in counts):
            empty_fiber_arrays += 1
            continue
        widths = [(count - 1).bit_length() for count in counts]
        # Enumerate all binary words, including padding ranks.  An invalid
        # rank gives a zero contribution, exactly as in a tensor encoding.
        for words in itertools.product(*(range(1 << width) for width in widths)):
            if any(word >= count for word, count in zip(words, counts)):
                invalid_words += 1
                continue
            by_pair = tuple(table.unrank_exact(b, rank)
                            for table, b, rank in zip(tables, allocations, words))
            beta = tuple(x for pair_tuple in by_pair for x in pair_tuple)
            assert beta not in recovered
            recovered.add(beta)
            encoded_sum = (encoded_sum + toy_product(by_pair, modulus)) % modulus
            valid_words += 1

    assert arrays == math.comb(strict_budget + len(DIRECTED_PAIRS) - 1,
                               len(DIRECTED_PAIRS))
    assert recovered == set(direct_tuples)
    assert valid_words == len(direct_tuples)
    assert encoded_sum == direct_sum
    return {
        "strict_budget": strict_budget,
        "modulus": modulus,
        "direct_exponent_tuples": len(direct_tuples),
        "exact_pair_budget_arrays": arrays,
        "arrays_with_an_empty_exact_fiber": empty_fiber_arrays,
        "valid_rank_words": valid_words,
        "invalid_padding_rank_words": invalid_words,
        "direct_sum": direct_sum,
        "encoded_sum": encoded_sum,
    }


def run_checks():
    start = time.perf_counter()
    counts = {
        "weight_lists": 0,
        "exact_fibers": 0,
        "exact_rank_round_trips": 0,
        "cumulative_budgets": 0,
        "cumulative_rank_round_trips": 0,
        "invalid_rank_checks": 0,
    }
    max_total = 8
    for length in range(4):
        for weights in itertools.product(range(1, 4), repeat=length):
            table = WeightedTuples(weights, max_total)
            all_tuples = brute_tuples_below(weights, max_total + 1)
            counts["weight_lists"] += 1
            for total in range(max_total + 1):
                exact = sorted(beta for beta in all_tuples
                               if sum(w * x for w, x in zip(weights, beta)) == total)
                assert table.count_exact(total) == len(exact)
                counts["exact_fibers"] += 1
                for rank, beta in enumerate(exact):
                    assert table.rank_exact(total, beta) == rank
                    assert table.unrank_exact(total, rank) == beta
                    counts["exact_rank_round_trips"] += 1
                try:
                    table.unrank_exact(total, len(exact))
                except ValueError:
                    counts["invalid_rank_checks"] += 1
                else:
                    raise AssertionError("A padding/out-of-range rank was accepted")
            for strict_budget in range(max_total + 2):
                below = sorted(
                    (beta for beta in all_tuples
                     if sum(w * x for w, x in zip(weights, beta)) < strict_budget),
                    key=lambda beta: (sum(w * x for w, x in zip(weights, beta)), beta))
                assert table.count_below(strict_budget) == len(below)
                counts["cumulative_budgets"] += 1
                for rank, beta in enumerate(below):
                    assert table.rank_below(strict_budget, beta) == rank
                    assert table.unrank_below(strict_budget, rank) == beta
                    counts["cumulative_rank_round_trips"] += 1

    three_group = [check_three_group_identity(budget, modulus)
                   for budget in range(1, 7) for modulus in (97, 101)]
    assert any(result["invalid_padding_rank_words"] > 0 for result in three_group)
    return {
        "status": "all checks passed",
        "counts": counts,
        "three_group_identities": three_group,
        "elapsed_seconds": round(time.perf_counter() - start, 6),
        "scope": "Exact weighted-tuple ranking and group-pair mode-index compression only; no low-degree local factorization or faster SAT solver is established.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    print(json.dumps(run_checks(), indent=2))


if __name__ == "__main__":
    main()
