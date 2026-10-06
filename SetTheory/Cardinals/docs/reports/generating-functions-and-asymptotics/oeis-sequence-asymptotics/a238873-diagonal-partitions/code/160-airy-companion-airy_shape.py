#!/usr/bin/env python3
"""Bounded Report160 companion, Python 3.10+, standard library only.

Exact integer/Fraction checks and explicitly approximate illustrations are
separate commands. No finite run proves an asymptotic theorem. This module
does not evaluate an Airy function or infer an effective asymptotic onset.
It writes JSON only to stdout; there is no file-writing or network API.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
import math
import os
from pathlib import Path
import re
import stat
import sys

MAX_N = 400
MAX_ENUMERATE = 32
MAX_VECTOR = 8
MAX_MULTIPLICITY = 8
MAX_SURVIVAL = 20
MAX_TAIL_J = 12
MAX_THRESHOLD = 10 ** 200
MAX_JSON_BYTES = 2 * 1024 * 1024
SOURCE_PATH = Path(__file__).absolute().parent.parent / 'data' / 'oeis_prefix.json'
B = math.log(2.0)
C = math.pi ** 2 / 12 + B * B
# Supplied decimal, not a computed/certified root: NIST DLMF Table 9.9.1.
ZETA_TABLE = 2.3381074105
ZETA_URL = 'https://dlmf.nist.gov/9.9.T1'


class InputError(ValueError):
    """Invalid type, domain, input source, or workload."""


class CheckFailure(RuntimeError):
    """A finite check failed; checks remain enabled under python -O."""


def integer(value, name, lower=0, upper=MAX_N):
    if type(value) is not int or not lower <= value <= upper:
        raise InputError(f'{name} must be an actual int in [{lower}, {upper}]; bool and float are refused')
    return value


def real(value, name, lower, upper):
    # Check integer size before float conversion to avoid unbounded conversion.
    if type(value) not in (int, float) or not lower <= value <= upper:
        raise InputError(f'{name} must be a finite int or float in [{lower}, {upper}]; bool is refused')
    value = float(value)
    if not math.isfinite(value):
        raise InputError(f'{name} must be finite')
    return value


def probability(value, name='probability'):
    if (type(value) is not Fraction or not 0 < value < 1
            or value.denominator > 100):
        raise InputError(f'{name} must be a Fraction in (0,1) with denominator <= 100')
    return value


def check(condition, message):
    if not condition:
        raise CheckFailure(message)


def counts_by_length(max_n=MAX_N):
    """Return exact a[n][k] for 0<=n<=max_n and 0<=k<=floor((sqrt(8N+1)-1)/2).

    After processing part size j, d[k][w] counts valid lists with largest
    part <=j. The recurrence is d_j(k,w)=d_(j-1)(k,w)+d_j(k-1,w-j),
    with k<=j. The second term removes one largest part j. Conversely,
    appending j preserves all earlier cumulative caps and the last cap is
    exactly k<=j. Increasing k updates implement that recurrence in place.
    The staircase lower bound k(k+1)/2<=w supplies a global length cap.
    Runtime O(N^2 sqrt(N)); memory O(N sqrt(N)); N is capped at 400.
    """
    integer(max_n, 'max_n')
    kmax = (math.isqrt(8 * max_n + 1) - 1) // 2
    d = [[0] * (max_n + 1) for _ in range(kmax + 1)]
    d[0][0] = 1
    for j in range(1, max_n + 1):
        for k in range(1, min(j, kmax) + 1):
            row, preceding = d[k], d[k - 1]
            for w in range(j, max_n + 1):
                row[w] += preceding[w - j]
    return [[d[k][n] for k in range(kmax + 1)] for n in range(max_n + 1)]


def counts(max_n=MAX_N):
    return [sum(row) for row in counts_by_length(max_n)]


def ordinary_counts(max_n=MAX_N):
    """Independent ordinary-partition coin change; no barrier or length state."""
    integer(max_n, 'max_n')
    values = [1] + [0] * max_n
    for j in range(1, max_n + 1):
        for n in range(j, max_n + 1):
            values[n] += values[n - j]
    return values


def partitions(n):
    """Independent recursive enumeration in increasing order, including ()."""
    integer(n, 'n', 0, MAX_ENUMERATE)
    def extend(remaining, minimum, prefix):
        if remaining == 0:
            yield prefix
        else:
            for value in range(minimum, remaining + 1):
                yield from extend(remaining - value, value, prefix + (value,))
    return extend(n, 1, ())


def _partition(parts, max_weight=MAX_N):
    if type(parts) not in (tuple, list) or len(parts) > MAX_N:
        raise InputError('parts must be a bounded list or tuple')
    for part in parts:
        integer(part, 'part', 1, MAX_N)
    if sum(parts) > max_weight or any(a > b for a, b in zip(parts, parts[1:])):
        raise InputError('parts must be increasing with bounded total weight')
    return tuple(parts)


def indexed_constraint(parts):
    return all(part >= i for i, part in enumerate(_partition(parts), 1))


def cumulative_constraint(parts):
    parts = _partition(parts)
    multiplicities = Counter(parts)
    cumulative = 0
    for j in range(1, parts[-1] + 1 if parts else 1):
        cumulative += multiplicities[j]
        if cumulative > j:
            return False
    return True


def monotonicity_image(parts):
    parts = _partition(parts, MAX_N - 1)
    if not indexed_constraint(parts):
        raise InputError('monotonicity map requires an admissible partition')
    return parts[:-1] + (parts[-1] + 1,) if parts else (1,)


def _multiplicities(vector):
    if type(vector) not in (tuple, list) or len(vector) > MAX_VECTOR:
        raise InputError(f'multiplicities must be a list or tuple of length <= {MAX_VECTOR}')
    for z in vector:
        integer(z, 'multiplicity', 0, MAX_MULTIPLICITY)
    return tuple(vector)


def prefix_statistics(vector):
    """Arbitrary prefixes are allowed, including paths going below zero."""
    vector = _multiplicities(vector)
    heights = [0]
    for z in vector:
        heights.append(heights[-1] + 1 - z)
    return {'M': len(vector), 'weight': sum(j * z for j, z in enumerate(vector, 1)),
            'length': sum(vector), 'heights': heights,
            'area': sum(heights[:-1]), 'endpoint': heights[-1]}


def prefix_identity(vector, q):
    """Exact q=e^(-t) version of the prefix change of measure.

    The terminal factor is (2q^M)^(-H_M), including its sign.
    The returned pair is (q^W, D_M P(prefix) q^area (2q^M)^(-H_M)).
    """
    probability(q, 'q')
    s = prefix_statistics(vector)
    M = s['M']
    D = Fraction(4) ** M * q ** (M * (M + 1) // 2)
    mass = Fraction(1, 2) ** (M + s['length'])
    W = q ** s['area'] * (2 * q ** M) ** (-s['endpoint'])
    return q ** s['weight'], D * mass * W


def full_identity(vector, M, q):
    """Finite-product pointwise identity; no tail truncation is called infinite."""
    vector = _multiplicities(vector)
    integer(M, 'M', 0, len(vector))
    probability(q, 'q')
    prefix = prefix_statistics(vector[:M])
    D = Fraction(4) ** M * q ** (M * (M + 1) // 2)
    P = Fraction(1)
    mass = Fraction(1, 2) ** (M + prefix['length'])
    for j, z in enumerate(vector[M:], M + 1):
        P /= 1 - q ** j
        mass *= (1 - q ** j) * q ** (j * z)
    W = q ** prefix['area'] * (2 * q ** M) ** (-prefix['endpoint'])
    weight = sum(j * z for j, z in enumerate(vector, 1))
    return q ** weight, D * P * mass * W


def exact_cutoffs(q):
    """Rational versions of floor(b/t) and ceil(b/t)+1, q=e^(-t).

    Powers, rather than floating logarithms, decide the equality case.
    Both returned cutoffs must fit the bounded prefix workload.
    """
    probability(q, 'q')
    half = Fraction(1, 2)
    upper = 0
    while upper <= MAX_VECTOR and q ** (upper + 1) >= half:
        upper += 1
    lower = upper + 1 if q ** upper == half else upper + 2
    if lower > MAX_VECTOR:
        raise InputError('cutoffs exceed the bounded prefix workload')
    return upper, lower


def finite_tail_counts(cutoff, largest_part, max_weight):
    integer(largest_part, 'largest_part', 0, MAX_TAIL_J)
    integer(cutoff, 'cutoff', 0, largest_part)
    integer(max_weight, 'max_weight')
    result = [1] + [0] * max_weight
    for j in range(cutoff + 1, largest_part + 1):
        for w in range(j, max_weight + 1):
            result[w] += result[w - j]
    return result


def finite_tail_normalization(q, cutoff, largest_part):
    probability(q, 'q')
    integer(largest_part, 'largest_part', 0, MAX_TAIL_J)
    integer(cutoff, 'cutoff', 0, largest_part)
    result = Fraction(1)
    for j in range(cutoff + 1, largest_part + 1):
        result /= 1 - q ** j
    return result


def survival(p, horizon):
    """Exact finite-horizon survival with geometric p; omitted jumps are killed.

    From deficit h, survival permits precisely 0<=Z<=h+1. Thus there is
    no numerical cutoff of the infinite geometric support in this DP.
    """
    probability(p, 'p')
    integer(horizon, 'horizon', 0, MAX_SURVIVAL)
    states = {0: Fraction(1)}
    for _ in range(horizon):
        following = {}
        for h, mass in states.items():
            for z in range(h + 2):
                key = h + 1 - z
                following[key] = following.get(key, Fraction(0)) + mass * (1 - p) * p ** z
        states = following
    return sum(states.values(), Fraction(0))


def _unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise InputError('duplicate source JSON key')
        result[key] = value
    return result


def _source_int(token):
    if len(token) > 100:
        raise InputError('source integer token is too long')
    return int(token)


def _refuse_number(_token):
    raise InputError('source JSON must contain only integer numeric tokens')


def read_prefix(path=SOURCE_PATH):
    """Read a bounded attributed numerical extract, never executable source.

    The default is a packaged local file. Other paths are for testing; no path
    is accepted through the CLI. A symlink leaf or nonregular file is refused.
    This is a bounded reader, not a filesystem access-control mechanism.
    """
    descriptor = None
    try:
        flags = os.O_RDONLY | os.O_NONBLOCK
        if hasattr(os, 'O_NOFOLLOW'):
            flags |= os.O_NOFOLLOW
        elif Path(path).is_symlink():
            raise InputError('source symlink is refused')
        descriptor = os.open(path, flags)
        info = os.fstat(descriptor)
        if not stat.S_ISREG(info.st_mode) or info.st_size > 32768:
            raise InputError('source must be a regular file of at most 32768 bytes')
        with os.fdopen(descriptor, 'rb') as stream:
            descriptor = None
            raw = stream.read(32769)
        if len(raw) > 32768:
            raise InputError('source exceeds 32768 bytes')
        doc = json.loads(raw.decode('utf-8'), object_pairs_hook=_unique_pairs,
                         parse_int=_source_int, parse_float=_refuse_number,
                         parse_constant=_refuse_number)
        required = {'schema', 'sequence', 'offset', 'source_url', 'source_revision',
                    'source_snapshot_sha256', 'transcription', 'terms'}
        if type(doc) is not dict or set(doc) != required:
            raise InputError('unexpected source structure')
        if (doc['schema'] != 'report160-oeis-prefix-v1' or doc['sequence'] != 'A238873'
                or doc['source_url'] != 'https://oeis.org/A238873'):
            raise InputError('unexpected source identity')
        integer(doc['offset'], 'offset', 0, 0)
        for key in ('source_revision', 'transcription'):
            if type(doc[key]) is not str or not 1 <= len(doc[key]) <= 500:
                raise InputError('invalid source attribution')
        if type(doc['source_snapshot_sha256']) is not str or not re.fullmatch('[0-9a-f]{64}', doc['source_snapshot_sha256']):
            raise InputError('invalid source digest')
        if type(doc['terms']) is not list or not 1 <= len(doc['terms']) <= MAX_N + 1:
            raise InputError('invalid source prefix length')
        for term in doc['terms']:
            integer(term, 'source term', 1, 10 ** 90)
        return doc
    except (OSError, TypeError, UnicodeError, json.JSONDecodeError, RecursionError) as exc:
        raise InputError('cannot read bounded source: ' + str(exc)) from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)


def counts_document(max_n=MAX_N):
    return {'schema': 'report160-counts-v1', 'sequence': 'A238873',
            'convention': 'Weakly increasing positive parts lambda_i >= i; A(0)=1.',
            'max_n': integer(max_n, 'max_n'), 'index_start': 0,
            'arithmetic': 'exact integers', 'counts': counts(max_n),
            'scope': 'Finite counts only; these values do not certify an asymptotic expansion.'}


def threshold_document(value, max_n=MAX_N):
    integer(value, 'value', 1, MAX_THRESHOLD)
    sequence = counts(max_n)
    first = next((n for n, count in enumerate(sequence) if count >= value), None)
    return {'schema': 'report160-exact-threshold-v1', 'target': value,
            'search_starts_at': 0, 'max_n': max_n, 'reached': first is not None,
            'first_n': first, 'count_at_first': sequence[first] if first is not None else None,
            'previous_count': sequence[first - 1] if first is not None and first else None,
            'last_count_searched': sequence[-1],
            'scope': 'Bounded exact first crossing only. An unreached target is not extrapolated.'}


def verify(max_n=MAX_N, enumerate_to=28):
    integer(max_n, 'max_n')
    integer(enumerate_to, 'enumerate_to', 0, MAX_ENUMERATE)
    if enumerate_to > max_n:
        raise InputError('enumerate_to cannot exceed max_n')
    table = counts_by_length(max_n)
    a = [sum(row) for row in table]
    ordinary = ordinary_counts(max_n)
    source = read_prefix()
    used = min(max_n + 1, len(source['terms']))
    check(a[:used] == source['terms'][:used], 'OEIS prefix mismatch')
    coverage = Counter({key: 0 for key in ('ordinary_partitions', 'admissible_partitions',
        'length_histograms', 'monotonicity_images', 'quantile_comparisons',
        'prefix_weight_identities', 'prefix_change_of_measure_identities',
        'full_product_identities', 'tail_retilting_identities', 'survival_horizons',
        'martingale_normalizations', 'cutoff_sign_cases', 'admissible_weight_domination')})
    for n in range(max_n + 1):
        check(1 <= a[n] <= ordinary[n], f'count bound at {n}')
        if n:
            check(a[n] >= a[n - 1], f'count monotonicity at {n}')
    for n in range(enumerate_to + 1):
        observed = Counter()
        images = set()
        ordinary_seen = 0
        for parts in partitions(n):
            ordinary_seen += 1
            coverage['ordinary_partitions'] += 1
            admissible = indexed_constraint(parts)
            check(admissible == cumulative_constraint(parts), 'constraint equivalence')
            if not admissible:
                continue
            coverage['admissible_partitions'] += 1
            observed[len(parts)] += 1
            mapped = monotonicity_image(parts)
            check(sum(mapped) == n + 1 and indexed_constraint(mapped), 'injection target')
            check(mapped not in images, 'injection collision')
            check(len(mapped) == 1 or mapped[-1] > mapped[-2], 'unique largest part')
            recovered = mapped[:-1] + (mapped[-1] - 1,) if parts else ()
            check(recovered == parts, 'injection inverse')
            images.add(mapped)
            coverage['monotonicity_images'] += 1
            # Exact generalized inverse C_j>=k iff lambda_k<=j, including j=0.
            cumulative = [sum(part <= j for part in parts) for j in range(n + 1)]
            for k, value in enumerate(parts, 1):
                for j, count in enumerate(cumulative):
                    check((value <= j) == (k <= count), 'row/cumulative inverse')
                    coverage['quantile_comparisons'] += 1
        check(ordinary_seen == ordinary[n], 'ordinary enumeration count')
        check([observed[k] for k in range(len(table[n]))] == table[n], 'length-resolved count')
        coverage['length_histograms'] += 1
    qs = (Fraction(1, 3), Fraction(1, 2), Fraction(2, 3))
    for M in range(6):
        for vector in product(range(4), repeat=M):
            s = prefix_statistics(vector)
            check(s['weight'] == M * (M + 1) // 2 + s['area'] - M * s['endpoint'], 'prefix weight identity')
            coverage['prefix_weight_identities'] += 1
            for q in qs:
                lhs, rhs = prefix_identity(vector, q)
                check(lhs == rhs, 'prefix normalization/sign')
                coverage['prefix_change_of_measure_identities'] += 1
    for vector in product(range(3), repeat=5):
        for M in (0, 1, 3, 5):
            for q in qs:
                lhs, rhs = full_identity(vector, M, q)
                check(lhs == rhs, 'finite full-product identity')
                coverage['full_product_identities'] += 1
    for q in (*qs, Fraction(3, 4), Fraction(4, 5), Fraction(9, 10)):
        M, lower = exact_cutoffs(q)
        check(q ** M >= Fraction(1, 2) > q ** (M + 1), 'upper floor cutoff')
        check(q ** 2 <= 2 * q ** lower <= q, 'lower terminal factor sign and range')
        coverage['cutoff_sign_cases'] += 1
        for vector in product(range(3), repeat=M):
            s = prefix_statistics(vector)
            if min(s['heights']) < 0:
                continue
            weight = q ** s['area'] * (2 * q ** M) ** (-s['endpoint'])
            check(0 < weight <= 1, 'admissible upper-cutoff weight domination')
            coverage['admissible_weight_domination'] += 1
    for cutoff, largest in ((0, 0), (0, 4), (2, 7), (5, 9)):
        coefficients = finite_tail_counts(cutoff, largest, 40)
        q, r = Fraction(2, 3), Fraction(3, 4)
        Zq = finite_tail_normalization(q, cutoff, largest)
        Zr = finite_tail_normalization(r, cutoff, largest)
        for w, coefficient in enumerate(coefficients):
            pq, pr = coefficient * q ** w / Zq, coefficient * r ** w / Zr
            check(pq == pr * (q / r) ** w * Zr / Zq, 'finite exact retilting')
            coverage['tail_retilting_identities'] += 1
    survival_rows = []
    for p in (Fraction(1, 4), Fraction(1, 3), Fraction(49, 100)):
        previous = Fraction(1)
        for horizon in range(MAX_SURVIVAL + 1):
            actual = survival(p, horizon)
            check(1 - 2 * p <= actual <= previous, 'finite survival inequality')
            previous = actual
            coverage['survival_horizons'] += 1
        r = (1 - p) / p
        check((1 - p) / (r * (1 - p * r)) == 1, 'martingale normalization')
        coverage['martingale_normalizations'] += 1
        survival_rows.append({'p': str(p), 'horizon': MAX_SURVIVAL,
            'finite_survival': str(previous), 'conservative_lower_bound': str(1 - 2 * p)})
    return {'schema': 'report160-finite-checks-v1', 'status': 'pass',
            'arithmetic': 'exact integers and rational strings; checks active under -O',
            'parameters': {'max_n': max_n, 'enumerate_to': enumerate_to},
            'oeis_terms_compared': used, 'coverage': dict(sorted(coverage.items())),
            'survival_examples': survival_rows,
            'scope': 'Finite algebra, indexing, enumeration, and inequalities only. No Airy asymptotic, local limit, infinite-horizon bound, concentration theorem, or effective threshold is certified by this run.'}


def density(x):
    x = real(x, 'x', 0, 10 ** 6)
    return 1.0 if x <= B else math.exp(-x) / -math.expm1(-x)


def cumulative_shape(x):
    x = real(x, 'x', 0, 10 ** 6)
    return x if x <= B else 2 * B + math.log1p(-math.exp(-x))


def row_shape(y):
    y = real(y, 'y', 0, 2 * B)
    if y >= 2 * B:
        raise InputError('row shape requires y < 2 log(2); its endpoint is infinite')
    # This form avoids subtracting two nearly equal floating-point numbers.
    return y if y <= B else -math.log(-math.expm1(y - 2 * B))


def airy_log_expression(n):
    """Two displayed asymptotic terms, NOT a finite-n error bound or estimate guarantee."""
    integer(n, 'n', 1, 10 ** 12)
    return 2 * math.sqrt(C * n) - ZETA_TABLE * B * C ** (-1 / 6) * n ** (1 / 6)


def threshold_expression(log_target):
    """Continuous two-term expression; never rounded to an asserted threshold."""
    u = real(log_target, 'log_target', 0, 10 ** 6)
    x = (u / (2 * math.sqrt(C))) ** 2
    return x + ZETA_TABLE * B * C ** (-2 / 3) * x ** (2 / 3)


def _decimal(value):
    if not math.isfinite(value):
        raise CheckFailure('nonfinite illustrative value')
    return format(value, '.12g')


def constants_document():
    li2 = math.fsum(2.0 ** (-r) / (r * r) for r in range(1, 81))
    # For r>=81, r^-2<=81^-2 and sum_(r>=81)2^-r=2^-80.
    tail_bound = 2.0 ** (-80) / (81 * 81)
    from_area = 1.5 * B * B + li2
    return {'b_log_2': _decimal(B), 'C': _decimal(C),
        'leading_B_2sqrtC': _decimal(2 * math.sqrt(C)),
        'zeta_table_supplied': '2.3381074105', 'zeta_source': ZETA_URL,
        'zeta_precision': 'DLMF Table 9.9.1 supplies 10 decimal places; no root is computed here.',
        'radial_airy_zeta_b': _decimal(ZETA_TABLE * B),
        'pointwise_airy_D': _decimal(ZETA_TABLE * B * C ** (-1 / 6)),
        'threshold_x_correction': _decimal(ZETA_TABLE * B * C ** (-2 / 3)),
        'length_over_sqrt_n': _decimal(2 * B / math.sqrt(C)),
        'critical_part_over_sqrt_n': _decimal(B / math.sqrt(C)),
        'Li2_half_80_term_series': _decimal(li2),
        'Li2_half_omitted_positive_series_bound': _decimal(tail_bound),
        'C_from_profile_area_series': _decimal(from_area),
        'area_identity_absolute_float_discrepancy': _decimal(abs(C - from_area)),
        'scope': 'All decimal values are illustrative ordinary floating point. The positive-series tail bound excludes rounding error and is not an interval enclosure.'}


def reference_length(t):
    """Truncated reference-law mean plus analytic bound on the omitted mean.

    Q_t is the product law, NOT the uniform conditioned partition law.
    """
    t = real(t, 't', 0.001, 0.5)
    J = math.ceil(40 / t)
    mean = math.fsum(density(t * j) for j in range(1, J + 1))
    first = math.exp(-t * (J + 1))
    tail_bound = first / (-math.expm1(-t) * (1 - first))
    return {'t': _decimal(t), 'cutoff_M': math.floor(B / t), 'last_summed_j': J,
            't_times_truncated_reference_mean_K': _decimal(t * mean),
            'omitted_t_mean_upper_bound': _decimal(t * tail_bound),
            'limiting_tK': _decimal(2 * B)}


def illustrations_document():
    table = counts_by_length(MAX_N)
    rows = []
    for n in (25, 50, 100, 200, 400):
        number = sum(table[n])
        mean = Fraction(sum(k * count for k, count in enumerate(table[n])), number)
        log_a = math.log(number)
        airy = airy_log_expression(n)
        rows.append({'n': n, 'exact_A_n': number, 'exact_mean_K': str(mean),
            'log_A_n_approx': _decimal(log_a), 'two_term_log_expression': _decimal(airy),
            'log_A_minus_two_term_expression': _decimal(log_a - airy),
            'mean_K_over_sqrt_n_approx': _decimal(float(mean) / math.sqrt(n)),
            'mean_tK_approx': _decimal(math.sqrt(C / n) * float(mean))})
    return {'schema': 'report160-illustrations-v1', 'constants': constants_document(),
            'finite_uniform_law': rows,
            'reference_product_law': [reference_length(t) for t in (0.2, 0.1, 0.05, 0.02, 0.01)],
            'continuous_threshold_expressions': [
                {'log_target': u, 'expression': _decimal(threshold_expression(u))}
                for u in (10, 100, 1000)],
            'scope': 'Exact counts and rational means are labeled separately. Other values are illustrative, not certified intervals. No finite error constant, onset, concentration certificate, or integer threshold follows from these examples.'}


def shape_document(points=121):
    integer(points, 'points', 3, 1001)
    # Two grids include the junction explicitly and stay away from y=2b.
    xs = sorted({6 * i / (points - 1) for i in range(points)} | {B})
    ys = sorted({1.98 * B * i / (points - 1) for i in range(points)} | {B})
    return {'schema': 'report160-shape-coordinates-v1', 'arithmetic': 'illustrative floating-point decimal strings',
            'coordinates': 'x=t*part_size; y=t*row_index; t=sqrt(C/n)',
            'junction': {'x': _decimal(B), 'y': _decimal(B)},
            'cumulative': [{'x': _decimal(x), 'g': _decimal(cumulative_shape(x)), 'm': _decimal(density(x))} for x in xs],
            'row': [{'y': _decimal(y), 'f': _decimal(row_shape(y))} for y in ys],
            'scope': 'Analytic limiting curves only; no sampled random partitions or finite-n confidence band. The row endpoint 2 log(2) is excluded. The diagonal segment does not count exact discrete contacts.'}


def encoded_json(document):
    try:
        result = json.dumps(document, indent=2, sort_keys=True, allow_nan=False) + '\n'
    except (TypeError, ValueError, RecursionError) as exc:
        raise InputError('document is not valid bounded JSON') from exc
    if len(result.encode('utf-8')) > MAX_JSON_BYTES:
        raise InputError('JSON output exceeds two MiB')
    return result


def cli_integer(token):
    if type(token) is not str or len(token) > 201 or not re.fullmatch(r'0|[1-9][0-9]*', token):
        raise argparse.ArgumentTypeError('expected a bounded unsigned decimal integer')
    return int(token)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('counts', help='exact A238873 coefficients')
    p.add_argument('--max-n', type=cli_integer, default=MAX_N)
    p = sub.add_parser('verify', help='bounded exact finite checks')
    p.add_argument('--max-n', type=cli_integer, default=MAX_N)
    p.add_argument('--enumerate-to', type=cli_integer, default=28)
    p = sub.add_parser('threshold', help='bounded exact first crossing')
    p.add_argument('--value', type=cli_integer, required=True)
    p.add_argument('--max-n', type=cli_integer, default=MAX_N)
    sub.add_parser('illustrations', help='separately labeled finite and approximate scalar values')
    p = sub.add_parser('shape', help='coordinates of the analytic limiting curves')
    p.add_argument('--points', type=cli_integer, default=121)
    args = parser.parse_args(argv)
    try:
        if args.command == 'counts':
            result = counts_document(args.max_n)
        elif args.command == 'verify':
            result = verify(args.max_n, args.enumerate_to)
        elif args.command == 'threshold':
            result = threshold_document(args.value, args.max_n)
        elif args.command == 'illustrations':
            result = illustrations_document()
        else:
            result = shape_document(args.points)
        sys.stdout.write(encoded_json(result))
        return 0
    except (InputError, CheckFailure) as exc:
        parser.exit(2, f'error: {exc}\n')


if __name__ == '__main__':
    raise SystemExit(main())
