#!/usr/bin/env python3
"""Report159: bounded exact subdiagonal-partition counts and cubic extraction.

Python 3.10+, standard library only. An increasing partition (lambda_i) is
subdiagonal when lambda_i <= i; the empty partition contributes s(0)=1.

  python -B companion.py counts --max-n 300
  python -B companion.py verify
  python -B companion.py expansion --order 3
  python -B companion.py threshold --value 1000000 --max-n 100

Use --out NEW.json for atomic no-clobber publication. Output parents must
already exist, belong to the current user, and not be group/world-writable.
Symlink components, traversal, special files, and non-.json targets are refused.
Safety assumes trusted parent directories and nonadversarial concurrency; it is
not a defence against an attacker able to rename ancestors or mutate files as
the current user. POSIX O_NOFOLLOW and hard links are required for file output.

Checks raise explicitly, also under -O. The finite reduction retains rectangle
exceptions in its finite checks; these counts are polynomially bounded, not
necessarily polynomial functions of n. Analytic extraction is deliberately
capped at order three and uses the separately audited shifted p/N expansions.
Finite calculations do not prove the analytic theorem, provide effective error
constants/onsets, or certify asymptotic inverse rounding.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
import json
import os
from pathlib import Path
import re
import secrets
import stat
import sys

MAX_N = 300
MAX_ENUM_N = 32
DEFAULT_ENUM_N = 28
MAX_ORDER = 3
MAX_CUTOFF = MAX_ORDER + 2
MAX_VECTOR_LENGTH = 5
MAX_VECTOR_ENTRY = 6
MAX_EXACT_VECTOR_ENTRY = 5
MAX_THRESHOLD = 10 ** 1000
MAX_JSON_BYTES = 2 * 1024 * 1024
SOURCE_PATH = Path(__file__).absolute().parent / 'data' / 'oeis_prefix.json'


class InputError(ValueError):
    """An input, bounded-workload, or safe-output precondition failed."""


class CheckFailure(RuntimeError):
    """An explicit mathematical check failed; checks survive python -O."""


def integer(value, name, lower=0, upper=MAX_N):
    if type(value) is not int or not lower <= value <= upper:
        raise InputError(f'{name} must be an integer in [{lower}, {upper}]; bool is refused')
    return value


def check(condition, message):
    if not condition:
        raise CheckFailure(message)


def vector(value, name, minimum_length=0):
    if type(value) not in (tuple, list) or not minimum_length <= len(value) <= MAX_VECTOR_LENGTH:
        raise InputError(f'{name} must be a list/tuple of length {minimum_length}..{MAX_VECTOR_LENGTH}')
    return tuple(integer(v, name + ' entry', 0, MAX_VECTOR_ENTRY) for v in value)


def subdiagonal_counts(max_n):
    """Positive DP by length k, weight n, and last (largest) part a.

    D_k(n,a) = sum_{b<=a} D_(k-1)(n-a,b), 1<=a<=k.
    Prefix sums implement the transition. D_0(0,0)=1. Summing over all
    lengths and largest parts gives s(n). Time O(max_n^3), space O(max_n^2).
    """
    integer(max_n, 'max_n')
    counts = [1] + [0] * max_n
    previous = [[0] for _ in range(max_n + 1)]
    previous[0][0] = 1
    for k in range(1, max_n + 1):
        following = [[0] * (k + 1) for _ in range(max_n + 1)]
        for weight in range(k - 1, max_n):
            prefix = previous[weight][0]
            for a in range(1, min(k, max_n - weight) + 1):
                if a < k:
                    prefix += previous[weight][a]
                following[weight + a][a] = prefix
                counts[weight + a] += prefix
        previous = following
    return counts


def partition_counts(max_n):
    """Independent unrestricted-partition coin-change recurrence."""
    integer(max_n, 'max_n')
    values = [1] + [0] * max_n
    for part in range(1, max_n + 1):
        for n in range(part, max_n + 1):
            values[n] += values[n - part]
    return values


def partitions(n):
    """Enumerate decreasing partitions, independently of the counting DP."""
    integer(n, 'n', 0, MAX_ENUM_N)
    def descend(remaining, largest, prefix):
        if not remaining:
            yield prefix
        for a in range(min(remaining, largest), 0, -1):
            yield from descend(remaining - a, a, prefix + (a,))
    return descend(n, n, ())


def _rank(mu):
    return mu[0] - len(mu) if mu else 0


def _row(mu, b):
    return mu[b - 1] if b <= len(mu) else 0


def _gaps(mu, length):
    return tuple(_row(mu, b) - _row(mu, b + 1) for b in range(1, length + 1))


def _meets(mu, x, y):
    counts = Counter(mu)
    return (all(counts[a] >= v for a, v in enumerate(x, 1))
            and all(a >= b for a, b in zip(_gaps(mu, len(y)), y)))


def _weight(x):
    return sum(a * v for a, v in enumerate(x, 1))


def _insert_rows(mu, x):
    return tuple(sorted(mu + tuple(a for a, v in enumerate(x, 1) for _ in range(v)), reverse=True))


def _remove_rows(mu, x):
    counts = Counter(mu)
    for a, v in enumerate(x, 1):
        check(counts[a] >= v, 'row removal lacks the required multiplicity')
        counts[a] -= v
    return tuple(a for a in sorted(counts, reverse=True) for _ in range(counts[a]))


def _insert_columns(mu, y):
    check(len(mu) >= len(y), 'column insertion requires enough good-region rows')
    return tuple(a + sum(y[j:]) if j < len(y) else a for j, a in enumerate(mu))


def _remove_columns(mu, y):
    check(all(a >= b for a, b in zip(_gaps(mu, len(y)), y)), 'column removal violates a gap bound')
    result = tuple(a - sum(y[j:]) if j < len(y) else a for j, a in enumerate(mu))
    check(all(a >= 0 for a in result) and all(a >= b for a, b in zip(result, result[1:])),
          'column removal did not produce a partition')
    return tuple(a for a in result if a)


def mixed_identity(n, r, x, y, cumulative=False):
    """Exact bounded mixed lower-bound identity, including both exceptions.

    For B=len(y)>0: source-bad means nu_B<=A, target-bad means
    mu_B<=A+y_B. For B=0, use largest part<=A on each side. Empty
    partitions have rank 0 and padded rows 0. Negative source weights
    contribute zero. Cumulative rank is allowed only for B=0.
    """
    integer(n, 'n', 0, MAX_ENUM_N)
    integer(r, 'r', -MAX_N, MAX_N)
    x, y = vector(x, 'x'), vector(y, 'y')
    if type(cumulative) is not bool or (cumulative and y):
        raise InputError('cumulative must be bool and can be true only for y=()')
    u, v, w = sum(x), sum(y), _weight(x) + _weight(y)
    a, b = len(x), len(y)
    accepts = (lambda mu, bound: _rank(mu) <= bound) if cumulative else (lambda mu, bound: _rank(mu) == bound)
    targets = [mu for mu in partitions(n) if accepts(mu, r) and _meets(mu, x, y)]
    sources = [mu for mu in partitions(n - w) if accepts(mu, r + u - v)] if n >= w else []
    bad_source = sum(_row(mu, b or 1) <= a for mu in sources)
    bad_target = sum(_row(mu, b or 1) <= a + (y[-1] if b else 0) for mu in targets)
    return {'actual': len(targets), 'shifted_rank_count': len(sources),
            'bad_source': bad_source, 'bad_target': bad_target,
            'reduced': len(sources) - bad_source + bad_target,
            'source_weight': n - w, 'source_rank': r + u - v}


def weak_vectors(total, length):
    integer(total, 'total', 0, MAX_CUTOFF)
    integer(length, 'length', 0, MAX_CUTOFF)
    def recur(left, slots, prefix):
        if slots == 0:
            if left == 0:
                yield prefix
        else:
            for a in range(left + 1):
                yield from recur(left - a, slots - 1, prefix + (a,))
    return recur(total, length, ())


def endpoint_patterns(cutoff):
    """Disjoint first-failure patterns for bottom indices <=M, top <=M+1."""
    integer(cutoff, 'cutoff', 2, MAX_CUTOFF)
    bottom, top = [], []
    for i in range(2, cutoff + 1):
        for head in weak_vectors(i - 1, i - 1):
            if all(sum(head[:h]) >= h for h in range(1, i)):
                bottom.append(head + (0,))
    for i in range(1, cutoff + 1):
        for d in range(i):
            for head in weak_vectors(i - 1 - d, i - 1):
                if all(sum(head[:h]) >= h - d for h in range(1, i)):
                    top.append((d, head + (0,)))
    return bottom, top


def _subset_shifts(length):
    result = []
    for mask in range(1 << length):
        chosen = [i + 1 for i in range(length) if mask >> i & 1]
        result.append((len(chosen), sum(chosen), (-1) ** len(chosen)))
    return result


def endpoint_reduction(cutoff):
    """Return shifted p/N terms for P_1(n-1)-E_n^(M), modulo exceptions.

    Exact marked coordinates are lower-bound finite differences. Cumulative
    rank terms are converted by rank symmetry. This list omits the explicitly
    enumerable polynomially bounded rectangle corrections; it is not an exact
    finite-n formula by itself. The endpoint tail is O_M(beta^(M-1)*p(n)).
    """
    integer(cutoff, 'cutoff', 2, MAX_CUTOFF)
    terms = defaultdict(Fraction)
    def add(kind, r, w, c):
        terms[kind, abs(r) if kind == 'N' else r, w] += c
    add('P', 1, 1, Fraction(1))
    bottom, top = endpoint_patterns(cutoff)
    shifts = {i: _subset_shifts(i) for i in range(1, cutoff + 1)}
    for x in bottom:
        for u, w, sign in shifts[len(x)]:
            add('P', sum(x) + u, _weight(x) + w, -sign)
    for d, y in top:
        for v, w, sign in shifts[len(y)]:
            add('N', -d + 1 - sum(y) - v, 1 + _weight(y) + w, -sign)
    for x in bottom:
        for d, y in top:
            for u, wa, sa in shifts[len(x)]:
                for v, wb, sb in shifts[len(y)]:
                    add('N', -d + sum(x) - sum(y) + u - v, _weight(x) + _weight(y) + wa + wb, sa * sb)
    for (kind, r, w), c in list(terms.items()):
        if kind != 'P':
            continue
        add('p', 0, w, c / 2)
        add('N', 0, w, c / 2 if r >= 0 else -c / 2)
        for j in range(1, r + 1 if r >= 0 else -r):
            add('N', j, w, c if r >= 0 else -c)
        del terms[kind, r, w]
    return {key: value for key, value in terms.items() if value}


# A polynomial in t=6/pi^2 is an ascending tuple of exact rational coefficients.
# No symbolic dependency, local-theta summation, or derivative-transfer premise.
def _poly(*values):
    result = tuple(Fraction(v) for v in values)
    while len(result) > 1 and result[-1] == 0:
        result = result[:-1]
    return result or (Fraction(0),)


def _poly_sum(left, right):
    return _poly(*( (left[i] if i < len(left) else 0) + (right[i] if i < len(right) else 0)
                    for i in range(max(len(left), len(right))) ))


def _poly_scale(poly, scalar):
    return _poly(*(coefficient * scalar for coefficient in poly))


def shifted_expansion(kind, r, w, order=MAX_ORDER):
    """Audited fixed-rank/fixed-shift coefficients through beta^3, only.

    The N formula comes directly from Zhou's Theorem 4.1, k=2,m=0,
    j=|r|, and division by the smooth partition expansion. It is not a
    claim of arbitrary-order analytic transfer from a local power series.
    """
    if type(kind) is not str or kind not in ('p', 'N'):
        raise InputError("kind must be 'p' or 'N'")
    integer(r, 'r', -32, 32)
    integer(w, 'w', 0, 100)
    integer(order, 'order', 0, MAX_ORDER)
    if kind == 'p' and r != 0:
        raise InputError('ordinary partition terms must have rank field zero')
    if kind == 'p':
        result = [_poly(1), _poly(-w), _poly(Fraction(w*w, 2), w),
                  _poly(-Fraction(w**3, 6), -Fraction(w, 48) - Fraction(5*w*w, 4), -Fraction(w, 4))]
    else:
        result = [_poly(0), _poly(Fraction(1, 4)),
                  _poly(Fraction(3, 16) - Fraction(w, 4), -Fraction(1, 4)),
                  _poly(Fraction(53, 192) - Fraction(r*r, 16) - Fraction(3*w, 16) + Fraction(w*w, 8),
                        -Fraction(89, 192) + Fraction(5*w, 8), Fraction(1, 16))]
    return result[:order + 1]


def expansion_document(order=MAX_ORDER):
    integer(order, 'order', 0, MAX_ORDER)
    cutoff = order + 2
    terms = endpoint_reduction(cutoff)
    answer = [_poly(0) for _ in range(order + 1)]
    for (kind, r, w), coefficient in terms.items():
        for j, poly in enumerate(shifted_expansion(kind, r, w, order)):
            answer[j] = _poly_sum(answer[j], _poly_scale(poly, coefficient))
    bottom, top = endpoint_patterns(cutoff)
    expected = [_poly(Fraction(1, 2)), _poly(-Fraction(1, 8)),
                _poly(-Fraction(11, 32), Fraction(1, 8)),
                _poly(-Fraction(317, 384), Fraction(329, 384), -Fraction(1, 32))]
    check(answer == expected[:order + 1], 'exact endpoint coefficient mismatch')
    return {
        'schema': 'report159-endpoint-expansion-v1', 'order': order, 'endpoint_cutoff_M': cutoff,
        'arithmetic': 'standard-library Fraction; ascending rational polynomial coefficients',
        'beta': 'pi/sqrt(6*n)', 'polynomial_variable': 't=6/pi^2',
        'coefficients_in_t': [[str(v) for v in poly] for poly in answer],
        'coefficients_in_pi_inverse_squared': [[str(v * 6**k) for k, v in enumerate(poly)] for poly in answer],
        'bottom_first_failure_patterns': len(bottom), 'top_first_failure_patterns': len(top),
        'bottom_top_intersections': len(bottom) * len(top), 'nonzero_shift_terms': len(terms),
        'shift_terms': [{'kind': kind, 'rank': r, 'weight_shift': w, 'coefficient': str(c)}
                        for (kind, r, w), c in sorted(terms.items())],
        'analytic_input': 'Audited fixed-rank and fixed-shift expansions through beta^3 only; Zhou Theorem 4.1, k=2,m=0,j=abs(r), and the smooth Rademacher partition term.',
        'source_url': 'https://arxiv.org/abs/2110.11174',
        'remainder_order_in_beta': order + 1,
        'scope': 'The shift list omits explicitly enumerable polynomially bounded rectangle corrections, whose ratios to p(n) are beyond every fixed algebraic order. The uniform endpoint tail with M=R+2 has order beta^(R+1). No fourth coefficient, general derivative-transfer claim, convergence claim, numerical error bound, effective onset, or asymptotic inverse rounding is supplied.'
    }


def counts_document(max_n=MAX_N):
    integer(max_n, 'max_n')
    return {'schema': 'report159-counts-v1', 'arithmetic': 'exact integers',
            'index_start': 0, 'max_n': max_n, 'subdiagonal': subdiagonal_counts(max_n),
            'ordinary_partitions': partition_counts(max_n),
            'convention': 'Weakly increasing positive parts lambda_i<=i; empty partition s(0)=p(0)=1.',
            'algorithm': 'Positive DP by length, weight, and largest part; prefix-sum transition. Ordinary p(n) uses independent coin-change DP.',
            'scope': 'Finite exact values only; these counts do not establish asymptotic error constants or an effective onset.'}


def threshold_document(value, max_n=MAX_N):
    integer(value, 'value', 1, MAX_THRESHOLD)
    integer(max_n, 'max_n', 0, MAX_N)
    counts = subdiagonal_counts(max_n)
    first = next((n for n in range(0, max_n + 1) if counts[n] >= value), None)
    return {'schema': 'report159-threshold-v1', 'value': value, 'max_n': max_n,
            'search_starts_at': 0, 'first_n': first, 'reached': first is not None,
            'count_at_first': counts[first] if first is not None else None,
            'previous_count': counts[first - 1] if first is not None and first > 0 else None,
            'last_count_searched': counts[-1],
            'method': 'Exact bounded positive DP; no asymptotic estimate is used.',
            'scope': 'If reached is false, only min{n>=0:s(n)>=value}>max_n is established; no larger threshold is guessed.'}


def pattern_identity(n, r, x, y, exact_rows=True, cumulative=False):
    """Exact finite-difference box identity with signed rectangle corrections.

    Row coordinates are exact unless exact_rows=False (used for top-only
    patterns with at least one 1). All marked gap coordinates are exact.
    """
    integer(n, 'n', 0, MAX_ENUM_N)
    integer(r, 'r', -MAX_N, MAX_N)
    x, y = vector(x, 'x'), vector(y, 'y')
    if type(exact_rows) is not bool or type(cumulative) is not bool or (cumulative and y):
        raise InputError('pattern flags must be bool; cumulative rank requires y=()')
    if ((exact_rows and any(v > MAX_EXACT_VECTOR_ENTRY for v in x))
            or any(v > MAX_EXACT_VECTOR_ENTRY for v in y)):
        raise InputError('exact marked values must be at most 5, leaving room for one lower-bound difference')
    actual = 0
    for mu in partitions(n):
        rank_ok = _rank(mu) <= r if cumulative else _rank(mu) == r
        row_ok = all(mu.count(a) == z if exact_rows else mu.count(a) >= z for a, z in enumerate(x, 1))
        if rank_ok and row_ok and _gaps(mu, len(y)) == y:
            actual += 1
    rank_sum = source_sum = target_sum = 0
    for row_mask in range(1 << len(x)) if exact_rows else (0,):
        xx = tuple(v + ((row_mask >> i) & 1) for i, v in enumerate(x))
        for gap_mask in range(1 << len(y)):
            yy = tuple(v + ((gap_mask >> i) & 1) for i, v in enumerate(y))
            sign = (-1) ** (row_mask.bit_count() + gap_mask.bit_count())
            terms = mixed_identity(n, r, xx, yy, cumulative)
            rank_sum += sign * terms['shifted_rank_count']
            source_sum += sign * terms['bad_source']
            target_sum += sign * terms['bad_target']
    return {'actual': actual, 'shifted_rank_sum': rank_sum, 'signed_bad_source': source_sum,
            'signed_bad_target': target_sum, 'reduced': rank_sum - source_sum + target_sum}


def _finite_map_checks(ps):
    """Finite independent enumerations and both directions of the repaired map."""
    maximum = len(ps) - 1
    xvectors = [(), (0,), (1,), (2,), (0, 1), (1, 1), (2, 0)]
    yvectors = [(0,), (1,), (2,), (0, 0), (0, 1), (1, 1), (0, 2)]
    stats = Counter()
    ranks = {n: Counter(_rank(mu) for mu in mus) for n, mus in ps.items()}
    bad_sources = {}
    for x, y in product(xvectors, yvectors):
        a, b = len(x), len(y)
        u, v, w = sum(x), sum(y), _weight(x) + _weight(y)
        stats['mixed_vector_pairs'] += 1
        if (a, b) not in bad_sources:
            bad_sources[a, b] = {n: Counter(_rank(mu) for mu in mus if _row(mu, b) <= a)
                                  for n, mus in ps.items()}
        actual, bad_target, good_target = Counter(), Counter(), Counter()
        for n, mus in ps.items():
            for mu in mus:
                if not _meets(mu, x, y):
                    continue
                r = _rank(mu)
                actual[n, r] += 1
                if _row(mu, b) <= a + y[-1]:
                    bad_target[n, r] += 1
                else:
                    good_target[n, r] += 1
                    core = _remove_rows(_remove_columns(mu, y), x)
                    check(_row(core, b) > a and sum(core) == n - w and _rank(core) == r + u - v,
                          'inverse good-map weight/rank/rectangle mismatch')
                    check(_insert_columns(_insert_rows(core, x), y) == mu
                          and _insert_rows(_insert_columns(core, y), x) == mu,
                          'inverse good-map reconstruction/commutation mismatch')
                    stats['inverse_good_maps'] += 1
        images, predicted = set(), Counter()
        for size, mus in ps.items():
            if size + w > maximum:
                continue
            for core in mus:
                if _row(core, b) <= a:
                    continue
                after_rows = _insert_rows(core, x)
                mu = _insert_columns(after_rows, y)
                check(mu == _insert_rows(_insert_columns(core, y), x), 'good insertions do not commute')
                check(sum(mu) == size + w and _rank(mu) == _rank(core) - u + v,
                      'forward good-map weight/rank mismatch')
                check(_row(mu, b) == _row(core, b) + y[-1] > a + y[-1] and _meets(mu, x, y),
                      'forward good-map lower-bound/rectangle mismatch')
                check(_remove_rows(_remove_columns(mu, y), x) == core, 'forward map is not inverted')
                check(mu not in images, 'forward good-map collision')
                images.add(mu)
                predicted[size + w, _rank(mu)] += 1
                # Row insertion may alter boundary G_B, but not earlier gaps.
                check(_gaps(core, b)[:-1] == _gaps(after_rows, b)[:-1], 'nonboundary top gap changed')
                if _gaps(core, b)[-1] != _gaps(after_rows, b)[-1]:
                    stats['boundary_gap_changes_observed'] += 1
                stats['forward_good_maps'] += 1
        check(predicted == good_target, 'good source and target sets disagree')
        for n in range(maximum + 1):
            for r in range(-maximum, maximum + 1):
                core = ranks[n - w][r + u - v] if n >= w else 0
                bad = bad_sources[a, b][n - w][r + u - v] if n >= w else 0
                check(actual[n, r] == core - bad + bad_target[n, r], 'mixed lower-bound identity mismatch')
                stats['mixed_rank_weight_identities'] += 1
    for x in xvectors:
        a, u, w = len(x), sum(x), _weight(x)
        actual = {n: Counter(_rank(mu) for mu in mus if _meets(mu, x, ())) for n, mus in ps.items()}
        bad_target = {n: Counter(_rank(mu) for mu in mus if _meets(mu, x, ()) and _row(mu, 1) <= a)
                      for n, mus in ps.items()}
        bad_source = {n: Counter(_rank(mu) for mu in mus if _row(mu, 1) <= a) for n, mus in ps.items()}
        for n in range(maximum + 1):
            for r in range(-5, 6):
                for cumulative in (False, True):
                    def take(counts, rank):
                        return sum(v for k, v in counts.items() if k <= rank) if cumulative else counts[rank]
                    core = take(ranks[n - w], r + u) if n >= w else 0
                    bad = take(bad_source[n - w], r + u) if n >= w else 0
                    check(take(actual[n], r) == core - bad + take(bad_target[n], r),
                          'pure-row exact/cumulative identity mismatch')
                    stats['pure_row_rank_identities'] += 1
    return stats


def _endpoint_checks(ps):
    stats = Counter()
    for cutoff in range(2, MAX_CUTOFF + 1):
        bottom, top = endpoint_patterns(cutoff)
        for n, mus in ps.items():
            for mu in mus:
                if _rank(mu) > 0 or 1 not in mu:
                    continue
                d = -_rank(mu)
                z = tuple(mu.count(a) for a in range(1, cutoff + 1))
                gaps = _gaps(mu, cutoff)
                bottom_event = any(sum(z[:i]) <= i - 1 for i in range(2, cutoff + 1))
                top_event = any(d <= i - 1 and sum(gaps[:i]) <= i - 1 - d for i in range(1, cutoff + 1))
                bottom_matches = sum(z[:len(x)] == x for x in bottom)
                top_matches = sum(d == dd and gaps[:len(y)] == y for dd, y in top)
                check(bottom_matches == int(bottom_event), 'bottom first-failure classification/disjointness')
                check(top_matches == int(top_event), 'top first-failure classification/disjointness')
                check(int(bottom_event or top_event) == bottom_matches + top_matches - bottom_matches * top_matches,
                      'bottom/top union-intersection mismatch')
                stats['first_failure_union_checks'] += 1
                if n > (cutoff + 1) ** 2:
                    ascending, k = mu[::-1], len(mu)
                    actual_bottom = any(i <= k and ascending[i - 1] > i for i in range(2, cutoff + 1))
                    actual_top = any(j <= k and mu[j - 1] > k - j + 1 for j in range(2, cutoff + 2))
                    check(bottom_event == actual_bottom and top_event == actual_top, 'endpoint/padded-index equivalence')
                    stats['unpadded_endpoint_equivalences'] += 1
    return stats


def verify(max_n=MAX_N, enumerate_to=DEFAULT_ENUM_N):
    integer(max_n, 'max_n')
    integer(enumerate_to, 'enumerate_to', 0, MAX_ENUM_N)
    if enumerate_to > max_n:
        raise InputError('enumerate_to cannot exceed max_n')
    counts, unrestricted = subdiagonal_counts(max_n), partition_counts(max_n)
    stats = Counter()
    for n in range(max_n + 1):
        check(1 <= counts[n] <= unrestricted[n], 'positive/subset count bound')
        if n:
            check(counts[n] >= counts[n - 1], 'adjoin-one monotonicity')
        stats['count_bound_indices'] += 1
    source = read_prefix()
    used = min(max_n + 1, len(source['terms']))
    check(counts[:used] == source['terms'][:used], 'A238875 numeric prefix mismatch')
    ps = {n: tuple(partitions(n)) for n in range(enumerate_to + 1)}
    direct = []
    for n, mus in ps.items():
        good = sum(all(a <= i for i, a in enumerate(mu[::-1], 1)) for mu in mus)
        check(good == counts[n] and len(mus) == unrestricted[n], 'direct partition count mismatch')
        check(Counter(_rank(mu) for mu in mus) == Counter(-_rank(mu) for mu in mus), 'rank symmetry mismatch')
        if n:
            obstruction = sum(_rank(mu) <= 0 and 1 in mu and not all(a <= i for i, a in enumerate(mu[::-1], 1)) for mu in mus)
            predecessor = sum(_rank(mu) <= 1 for mu in ps[n - 1])
            check(good == predecessor - obstruction, 'exact baseline-minus-obstruction identity')
            stats['baseline_obstruction_identities'] += 1
        direct.append({'n': n, 's': good, 'p': len(mus)})
        stats['direct_partition_count_indices'] += 1
    stats.update(_finite_map_checks(ps))
    stats.update(_endpoint_checks(ps))
    box_limit = min(enumerate_to, 12)
    bottoms = [(1, 0), (1, 1, 0), (2, 0, 0)]
    tops = [(0, (0,)), (0, (1, 0)), (1, (0, 0))]
    for n in range(box_limit + 1):
        cases = [(0, x, (), True, True) for x in bottoms]
        cases += [(-d, (1,), y, False, False) for d, y in tops]
        cases += [(-d, x, y, True, False) for x in bottoms for d, y in tops]
        for r, x, y, exact_rows, cumulative in cases:
            result = pattern_identity(n, r, x, y, exact_rows, cumulative)
            check(result['actual'] == result['reduced'], 'finite mixed endpoint box identity')
            stats['finite_difference_box_identities'] += 1
            if result['signed_bad_source'] or result['signed_bad_target']:
                stats['box_identities_with_nonzero_exceptions'] += 1
    coefficients = []
    for order in range(MAX_ORDER + 1):
        output = expansion_document(order)
        coefficients.append({'order': order, 'cutoff': output['endpoint_cutoff_M'],
                             'nonzero_shift_terms': output['nonzero_shift_terms'],
                             'coefficients_in_t': output['coefficients_in_t']})
        stats['exact_symbolic_orders_checked'] += 1
    return {'schema': 'report159-finite-checks-v1', 'status': 'pass',
            'arithmetic': 'exact integers/Fractions; checks remain active under python -O',
            'parameters': {'max_n': max_n, 'enumerate_to': enumerate_to, 'box_identity_to': box_limit},
            'partitions_enumerated': sum(map(len, ps.values())), 'oeis_terms_compared': used,
            'coverage': dict(sorted(stats.items())), 'direct_counts': direct, 'symbolic_checks': coefficients,
            'boundary_gap_example': {'core': [2], 'inserted_rows': [1], 'after_rows': [2, 1], 'G_1_before': 2, 'G_1_after': 1,
                                     'explanation': 'Row insertion may change G_B. The subsequent column insertion establishes every required gap lower bound.'},
            'scope': 'Finite tests validate implementation/indexing, the corrected finite maps, explicit exceptional counts and cubic rational algebra. They do not prove the all-orders theorem or supply asymptotic error constants/onsets; exceptional counts are polynomially bounded, not asserted to be polynomial functions.'}


def _parent_directory(path, trusted):
    if os.name != 'posix' or not hasattr(os, 'O_NOFOLLOW'):
        raise InputError('safe file I/O requires POSIX O_NOFOLLOW')
    if not isinstance(path, (str, os.PathLike)):
        raise InputError('file path must be text or PathLike')
    raw = os.fspath(path)
    if not isinstance(raw, str) or not raw or len(raw) > 4096 or any(ord(c) < 32 or ord(c) == 127 for c in raw) or '\\' in raw:
        raise InputError('invalid file path')
    parts = raw.split('/')
    if raw.endswith('/') or any(x in ('.', '..') for x in parts) or any(not x for x in parts[1:]):
        raise InputError('empty, dot, parent, or trailing-slash path components are refused')
    if not raw.startswith('/'):
        raw = os.getcwd().rstrip('/') + '/' + raw
    parts = raw.split('/')[1:]
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    fd = os.open('/', flags)
    try:
        for part in parts[:-1]:
            following = os.open(part, flags, dir_fd=fd)
            os.close(fd)
            fd = following
        info = os.fstat(fd)
        if trusted and (info.st_uid != os.geteuid() or info.st_mode & 0o022):
            raise InputError('output parent must be owned by the current user and not group/world-writable')
        return fd, parts[-1]
    except BaseException:
        os.close(fd)
        raise


def encoded_json(document):
    try:
        data = (json.dumps(document, indent=2, sort_keys=True, allow_nan=False) + '\n').encode('utf-8')
    except (TypeError, ValueError, RecursionError) as exc:
        raise InputError('document cannot be encoded as bounded JSON') from exc
    if len(data) > MAX_JSON_BYTES:
        raise InputError('JSON output exceeds two MiB')
    return data


def write_new_json(path, document):
    """Atomic no-clobber publication through a pinned trusted directory fd.

    A complete private file is linked into the new name exclusively. An existing
    file, symlink, special file, or directory is always refused. A post-link fsync
    failure may leave a complete output present; do not blindly retry/delete it.
    """
    data = encoded_json(document)
    directory = fd = None
    temporary = None
    try:
        directory, leaf = _parent_directory(path, trusted=True)
        if not leaf.endswith('.json'):
            raise InputError('output filename must end in .json')
        try:
            os.stat(leaf, dir_fd=directory, follow_symlinks=False)
        except FileNotFoundError:
            pass
        else:
            raise InputError('output exists; choose a fresh filename (nothing is overwritten)')
        candidate = '.report159-' + secrets.token_hex(16) + '.tmp'
        fd = os.open(candidate, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                     0o600, dir_fd=directory)
        temporary = candidate
        with os.fdopen(fd, 'wb') as stream:
            fd = None
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, leaf, src_dir_fd=directory, dst_dir_fd=directory, follow_symlinks=False)
        os.unlink(temporary, dir_fd=directory)
        temporary = None
        os.fsync(directory)
    except OSError as exc:
        raise InputError('safe output failed: ' + str(exc)) from exc
    finally:
        if fd is not None:
            os.close(fd)
        if temporary is not None and directory is not None:
            try:
                os.unlink(temporary, dir_fd=directory)
            except FileNotFoundError:
                pass
        if directory is not None:
            os.close(directory)


def cli_integer(text):
    if type(text) is not str or len(text) > 1001 or re.fullmatch(r'0|[1-9][0-9]*', text) is None:
        raise argparse.ArgumentTypeError('expected a canonical nonnegative decimal integer')
    return int(text)




def _unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise InputError('duplicate JSON key: ' + key)
        result[key] = value
    return result


def _no_noninteger(token):
    raise InputError('noninteger or nonfinite JSON number is refused')


def _source_integer(token):
    if len(token) > 102:
        raise InputError('source JSON integer token is too long')
    return int(token)


def read_prefix(path=SOURCE_PATH):
    """Read bounded numerical data only; never execute source-supplied code."""
    directory = descriptor = None
    try:
        directory, leaf = _parent_directory(path, trusted=False)
        descriptor = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=directory)
        info = os.fstat(descriptor)
        if not stat.S_ISREG(info.st_mode) or info.st_size > 32768:
            raise InputError('prefix source must be a regular file of at most 32768 bytes')
        with os.fdopen(descriptor, 'rb') as stream:
            descriptor = None
            data = stream.read(32769)
        if len(data) > 32768:
            raise InputError('prefix source exceeds 32768 bytes')
        payload = json.loads(data.decode('utf-8'), object_pairs_hook=_unique_pairs,
                             parse_int=_source_integer, parse_float=_no_noninteger,
                             parse_constant=_no_noninteger)
        if type(payload) is not dict or payload.get('schema') != 'report159-oeis-prefix-v1':
            raise InputError('unexpected prefix source schema')
        if payload.get('sequence') != 'A238875' or payload.get('source_url') != 'https://oeis.org/A238875':
            raise InputError('unexpected sequence/source URL')
        integer(payload.get('offset'), 'offset', 0, 0)
        values = payload.get('terms')
        if type(values) is not list or not 1 <= len(values) <= MAX_N + 1:
            raise InputError('invalid numerical prefix length')
        for value in values:
            integer(value, 'prefix term', 0, 10 ** 100)
        return payload
    except (OSError, UnicodeError, json.JSONDecodeError, RecursionError) as exc:
        raise InputError('cannot read prefix source: ' + str(exc)) from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)
        if directory is not None:
            os.close(directory)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    actions = parser.add_subparsers(dest='action', required=True)
    for name in ('counts', 'verify', 'expansion', 'threshold'):
        sub = actions.add_parser(name)
        sub.add_argument('--out', help='fresh .json path in an existing trusted directory; default stdout')
        if name != 'expansion':
            sub.add_argument('--max-n', type=cli_integer, default=MAX_N)
        if name == 'verify':
            sub.add_argument('--enumerate-to', type=cli_integer, default=None)
        if name == 'expansion':
            sub.add_argument('--order', type=cli_integer, default=MAX_ORDER)
        if name == 'threshold':
            sub.add_argument('--value', type=cli_integer, required=True)
    args = parser.parse_args(argv)
    try:
        if args.action == 'counts':
            document = counts_document(args.max_n)
        elif args.action == 'verify':
            chosen = min(args.max_n, DEFAULT_ENUM_N) if args.enumerate_to is None else args.enumerate_to
            document = verify(args.max_n, chosen)
        elif args.action == 'expansion':
            document = expansion_document(args.order)
        else:
            document = threshold_document(args.value, args.max_n)
        if args.out is not None:
            write_new_json(args.out, document)
        else:
            sys.stdout.write(encoded_json(document).decode('utf-8'))
    except (InputError, CheckFailure) as exc:
        parser.exit(2, 'error: ' + str(exc) + '\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
