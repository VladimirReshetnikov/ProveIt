#!/usr/bin/env python3
"""Recover all ordinal order-map profiles from one finite Cantor-form probe.

For a poset with n>0 vertices the probe is
  Theta_n = sum_{j=0}^{n-1} omega^((n+1)^(n-1-j)).
Its maximal order type records the ordered-fiber signature without collisions.
This module also implements direct signature evaluation, independently of the
ideal-chain dynamic program in ordinal_maps.py.
"""
from __future__ import annotations

from collections import Counter
from itertools import combinations
import json
from pathlib import Path
from typing import Iterator

from ordinal_maps import (Ordinal, Poset, ZERO, ONE, natural_sum, omega_power,
                          order_map_type, order_map_type_direct)


def compositions(n: int) -> Iterator[tuple[int, ...]]:
    if type(n) is not int or n < 0:
        raise ValueError('n must be a nonnegative integer.')
    if n == 0:
        yield ()
        return
    for first in range(1, n + 1):
        for tail in compositions(n - first):
            yield (first,) + tail


def universal_probe(n: int) -> Ordinal:
    if type(n) is not int or n < 0:
        raise ValueError('n must be a nonnegative integer.')
    if n == 0:
        return ONE
    base = n + 1
    return Ordinal(tuple((Ordinal.finite(base ** (n - 1 - j)), 1)
                         for j in range(n)))


def signature_direct(poset: Poset, assignment_limit: int = 2_000_000
                     ) -> dict[tuple[int, ...], int]:
    """Counts surjective isotone maps, indexed by ordered nonzero fiber sizes."""
    if poset.n == 0:
        return {(): 1}
    if sum(k ** poset.n for k in range(1, poset.n + 1)) > assignment_limit:
        raise ValueError('Direct signature enumeration exceeds the safety limit.')
    counts: Counter[tuple[int, ...]] = Counter()
    for k in range(1, poset.n + 1):
        for values in poset.maps(k):
            hist = tuple(values.count(j) for j in range(k))
            if all(hist):
                counts[hist] += 1
    return dict(counts)


def signature_from_probe(poset: Poset) -> dict[tuple[int, ...], int]:
    """Read signature entries from the CNF coefficients of one probe value."""
    n = poset.n
    if n == 0:
        return {(): 1}
    coefficients = dict(order_map_type(poset, universal_probe(n)).terms)
    base = n + 1
    result = {}
    for comp in compositions(n):
        exponent = sum(size * base ** (n - 1 - j) for j, size in enumerate(comp))
        result[comp] = coefficients.get(Ordinal.finite(exponent), 0)
    return result


def type_from_signature(signature: dict[tuple[int, ...], int], n: int,
                        beta: Ordinal) -> Ordinal:
    """Evaluate the grouping-by-nonempty-blocks version of the main formula."""
    if n == 0:
        return ONE
    exponents = beta.expand_exponents()
    result = ZERO
    for comp, coefficient in signature.items():
        if sum(comp) != n or not comp or min(comp) <= 0 or coefficient <= 0:
            raise ValueError('Invalid ordered-fiber signature.')
        for chosen in combinations(range(len(exponents)), len(comp)):
            exponent = natural_sum(exponents[j].natural_times(size)
                                   for j, size in zip(chosen, comp))
            term = omega_power(exponent).natural_times(coefficient)
            result = result.natural_sum(term)
    return result


def run_checks() -> dict:
    from verify import natural_posets
    probes = recovered = evaluations = 0
    targets = [Ordinal.finite(0), Ordinal.finite(4),
               Ordinal.from_json({'cnf': [[1, 1], [0, 1]]}),
               Ordinal.from_json({'cnf': [[2, 2], [1, 1], [0, 1]]}),
               Ordinal.from_json({'cnf': [[{'cnf': [[1, 1], [0, 1]]}, 1], [1, 1]]})]
    for n in range(6):
        for poset in natural_posets(n):
            direct = signature_direct(poset)
            decoded = signature_from_probe(poset)
            assert direct == decoded, (n, poset.edges(), direct, decoded)
            probes += 1
            recovered += len(direct)
            for beta in targets:
                assert type_from_signature(decoded, n, beta) == order_map_type(poset, beta)
                evaluations += 1
    fork = Poset.from_edges(3, [(0, 1), (0, 2)])
    data = {
        'probe_decodings_checked': probes,
        'signature_coefficients_checked': recovered,
        'profile_evaluations_checked': evaluations,
        'failed_assertions': 0,
        'n3_probe': str(universal_probe(3)),
        'fork_map_probe_type': str(order_map_type(fork, universal_probe(3))),
        'fork_signature': {','.join(map(str, a)): c for a, c in signature_direct(fork).items()},
        'dual_fork_signature': {','.join(map(str, a)): c for a, c in signature_direct(fork.dual()).items()},
        'caveat': 'Finite symbolic checks do not establish transfinite correctness or novelty.'
    }
    root = Path(__file__).resolve().parent.parent
    (root / 'data' / 'profile_checks.json').write_text(json.dumps(data, indent=2) + '\n')
    return data


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Verification requires assertions; do not use python -O.')
    print(json.dumps(run_checks(), indent=2))
