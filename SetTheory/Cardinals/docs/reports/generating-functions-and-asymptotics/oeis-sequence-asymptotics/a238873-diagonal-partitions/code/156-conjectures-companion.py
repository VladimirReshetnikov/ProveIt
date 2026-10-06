#!/usr/bin/env python3
"""Report156: bounded, exact finite checks for two partition conjectures.

Python 3.10+, standard library only. All partitions are weakly increasing.
The multiplicity DP and descending-part enumeration are independent algorithms.
Finite computations are not proofs of asymptotics or exact growth constants.
The inverse initializer is floating-point and explicitly noncertifying.

Examples (run from the directory containing this file):
  python -B companion.py counts --max-n 200
  python -B companion.py verify --max-n 200 --enumerate-to 40 --prefix-to 10
  python -B companion.py threshold --value 1000 --max-n 200
  python -B companion.py inverse-model --value 1000000000
Use --out NEW.json to publish atomically without replacing an existing path.
No input/source files are ever overwritten. Output parents must exist, be
owned by the current user and not be group/world-writable. Symlink components,
existing targets of every kind, and non-JSON output suffixes are refused.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
import math
import os
from pathlib import Path
import re
import secrets
import stat
import sys

MAX_N = 200
MAX_ENUM_N = 40
MAX_PREFIX = 10
MAX_HEIGHT = 200
MAX_THRESHOLD = 10 ** 300
MAX_JSON_BYTES = 2 * 1024 * 1024
SOURCE_PATH = Path(__file__).absolute().parent / 'data' / 'oeis_prefixes.json'


class InputError(ValueError):
    """An input, precondition, or safe-output requirement was not satisfied."""


class CheckFailure(RuntimeError):
    """An explicit finite mathematical check failed (also under python -O)."""


class AllOnesException(InputError):
    """The all-ones partition is outside the fixed-rank map's domain."""


def integer(value, name, lower=0, upper=MAX_N):
    if type(value) is not int or not lower <= value <= upper:
        raise InputError(f'{name} must be an integer in [{lower}, {upper}]; bool is refused')
    return value


def check(condition, message):
    if not condition:
        raise CheckFailure(message)


def partition(value, *, empty=True):
    if not isinstance(value, (tuple, list)) or len(value) > MAX_N:
        raise InputError('partition must be a bounded tuple or list')
    if not empty and not value:
        raise InputError('partition must be nonempty')
    previous = 0
    weight = 0
    for part in value:
        integer(part, 'part', 1)
        if part < previous:
            raise InputError('parts must be weakly increasing')
        previous = part
        weight += part
    integer(weight, 'partition weight')
    return tuple(value)


def partitions(n):
    """Direct enumeration: choose descending parts, reverse each completed list."""
    integer(n, 'n', 0, MAX_ENUM_N)
    def descend(left, ceiling, selected):
        if left == 0:
            yield tuple(reversed(selected))
            return
        for v in range(min(left, ceiling), 0, -1):
            yield from descend(left - v, v, selected + (v,))
    return descend(n, n, ())


def subdiagonal(lam, shift=0):
    lam = partition(lam)
    integer(shift, 'shift')
    return all(v <= i + shift for i, v in enumerate(lam, 1))


def superdiagonal(lam):
    lam = partition(lam)
    return all(v >= i for i, v in enumerate(lam, 1))


def rank(lam):
    lam = partition(lam, empty=False)
    return lam[-1] - len(lam)


def conjugate(lam):
    lam = partition(lam)
    if not lam:
        return ()
    return tuple(sum(v >= j for v in lam) for j in range(lam[-1], 0, -1))


def diagonal_counts(max_n, kind, shift=0):
    """Multiplicity DP; states (weight, number of parts), processed by value.

    Appending t copies of v after k smaller parts is subdiagonal iff
    v <= k+1+shift, and superdiagonal iff v >= k+t. Empty blocks do not
    require either condition. This avoids enumerating individual partitions.
    """
    integer(max_n, 'max_n')
    integer(shift, 'shift')
    if kind not in ('sub', 'super'):
        raise InputError('kind must be sub or super')
    if kind == 'super' and shift != 0:
        raise InputError('shift is defined only for the subdiagonal class')
    states = {(0, 0): 1}
    for v in range(1, max_n + 1):
        updated = dict(states)  # choose zero copies of v
        for (weight, k), ways in states.items():
            limit = (max_n - weight) // v
            if kind == 'sub':
                if v > k + 1 + shift:
                    continue
            else:
                limit = min(limit, v - k)
            for t in range(1, limit + 1):
                key = weight + t * v, k + t
                updated[key] = updated.get(key, 0) + ways
        states = updated
    result = [0] * (max_n + 1)
    for (weight, _), ways in states.items():
        result[weight] += ways
    return result


def ordinary_counts(max_n):
    """Euler product coefficients, allowing repeated parts."""
    integer(max_n, 'max_n')
    result = [1] + [0] * max_n
    for v in range(1, max_n + 1):
        for n in range(v, max_n + 1):
            result[n] += result[n - v]
    return result


def distinct_counts(max_n, cutoff=0):
    """f_cutoff(n), including f(0)=1 and f(n)=0 for 1 <= n <= cutoff."""
    integer(max_n, 'max_n')
    integer(cutoff, 'cutoff')
    result = [1] + [0] * max_n
    for v in range(cutoff + 1, max_n + 1):
        for n in range(max_n, v - 1, -1):
            result[n] += result[n - v]
    return result


def coefficient(values, n):
    """Zero extension for a bounded coefficient vector at negative indices."""
    integer(n, 'coefficient index', -MAX_N * MAX_N, MAX_N)
    if n < 0:
        return 0
    if n >= len(values):
        raise InputError('coefficient index exceeds the computed range')
    return values[n]


def remove_ones(lam):
    """Fixed-rank injection; source rank is needed for its inverse."""
    lam = partition(lam, empty=False)
    j = lam.count(1)
    if j == len(lam):
        raise AllOnesException('all-ones sources are treated separately')
    if j == 0:
        return lam
    return lam[j:-1] + (lam[-1] + j,)


def restore_ones(nu, source_rank):
    """Inverse on the image; rejects tuples outside that image at this rank."""
    nu = partition(nu, empty=False)
    integer(source_rank, 'source_rank', 1 - MAX_N, MAX_N - 1)
    if nu[0] == 1:
        raise InputError('image partition must have no ones')
    delta = rank(nu) - source_rank
    if delta < 0 or delta % 2:
        raise InputError('rank difference must be a nonnegative even integer')
    j = delta // 2
    if j == 0:
        return nu
    if len(nu) > 1 and nu[-1] == nu[-2]:
        raise InputError('positive-j image must have a unique largest part')
    reduced = nu[-1] - j
    if reduced < 2 or (len(nu) > 1 and reduced < nu[-2]):
        raise InputError('decremented largest part cannot be an original largest part')
    source = (1,) * j + nu[:-1] + (reduced,)
    source = partition(source, empty=False)
    if rank(source) != source_rank or remove_ones(source) != nu:
        raise InputError('not in the image at the specified source rank')
    return source


def interior_hypotheses(lam, m, shift):
    lam = partition(lam, empty=False)
    integer(m, 'm', 1)
    integer(shift, 'shift')
    k = len(lam)
    return (k >= 2 * m + 1 and lam.count(1) >= m
            and lam[-1] <= k + shift - m
            and (m + 1) * (k - m + 1) > sum(lam))


def catalan(m):
    integer(m, 'm')
    return math.comb(2 * m, m) // (m + 1)


def prefixes(m, height=None):
    """Enumerate i <= lambda_i <= m, optionally lambda_i <= i+height-1."""
    integer(m, 'm', 0, MAX_PREFIX)
    if height is not None:
        integer(height, 'height', 1, MAX_HEIGHT)
    def grow(partial):
        i = len(partial) + 1
        if i > m:
            yield partial
            return
        top = m if height is None else min(m, i + height - 1)
        for v in range(max(i, partial[-1] if partial else 1), top + 1):
            yield from grow(partial + (v,))
    return grow(())


def bounded_walk_count(m, height):
    """(T_height ** (2*m))[0,0], computed only with exact integer arithmetic."""
    integer(m, 'm')
    integer(height, 'height', 0, MAX_HEIGHT)
    ways = [1] + [0] * height
    for _ in range(2 * m):
        following = [0] * (height + 1)
        for level, count in enumerate(ways):
            if level:
                following[level - 1] += count
            if level < height:
                following[level + 1] += count
        ways = following
    return ways[0]


def bounded_weight(m, height):
    integer(m, 'm')
    integer(height, 'height', 1, MAX_HEIGHT)
    return m * (m + 1) // 2 + (height - 1) * m


def prefix_to_walk(lam):
    """Reverse complement, then north/east path; returns every vertex height."""
    lam = partition(lam)
    m = len(lam)
    if any(v < i or v > m for i, v in enumerate(lam, 1)):
        raise InputError('not a Catalan prefix')
    mu = tuple(m + 1 - v for v in reversed(lam))
    x = y = 0
    levels = [0]
    for coordinate in mu:
        while x < coordinate - 1:
            x += 1
            levels.append(y - x)
        y += 1
        levels.append(y - x)
    while x < m:
        x += 1
        levels.append(y - x)
    return tuple(levels)


def counts_document(max_n=MAX_N):
    integer(max_n, 'max_n')
    return {
        'schema': 'report156-counts-v1', 'arithmetic': 'exact integers',
        'index_start': 0, 'max_n': max_n,
        'convention': 'weakly increasing positive parts; the empty partition counts at n=0',
        'algorithm': 'multiplicity DP for diagonal classes; Euler products for p and q',
        'sequences': {
            'A000041': ordinary_counts(max_n),
            'A000009': distinct_counts(max_n),
            'A238875': diagonal_counts(max_n, 'sub'),
            'A238873': diagonal_counts(max_n, 'super'),
        },
        'scope': 'Finite exact values only; no asymptotic proof or exact growth constant is inferred.'
    }


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


def read_prefixes(path=SOURCE_PATH):
    """Read the shipped, small numerical source extract, never arbitrary code."""
    directory = descriptor = None
    try:
        directory, leaf = _parent_directory(path, trusted=False)
        descriptor = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                             dir_fd=directory)
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
        if not isinstance(payload, dict) or payload.get('schema') != 'report156-oeis-prefixes-v1':
            raise InputError('unexpected prefix source schema')
        sources = payload.get('sequences')
        if not isinstance(sources, dict) or set(sources) != {'A000041', 'A000009', 'A238875', 'A238873'}:
            raise InputError('prefix source must contain the four expected sequences')
        for seq, record in sources.items():
            if not isinstance(record, dict) or record.get('source_url') != 'https://oeis.org/' + seq:
                raise InputError('unexpected sequence source URL')
            integer(record.get('offset'), 'offset', 0, 0)
            values = record.get('terms')
            if not isinstance(values, list) or not 1 <= len(values) <= MAX_N + 1:
                raise InputError('invalid numerical prefix length')
            for value in values:
                integer(value, 'prefix term', 0, 10 ** 100)
        return sources
    except (OSError, UnicodeError, json.JSONDecodeError, RecursionError) as exc:
        raise InputError('cannot read prefix source: ' + str(exc)) from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)
        if directory is not None:
            os.close(directory)


def verify(max_n=MAX_N, enumerate_to=MAX_ENUM_N, prefix_to=MAX_PREFIX):
    """Return a deterministic coverage record; every check uses explicit raises."""
    integer(max_n, 'max_n')
    integer(enumerate_to, 'enumerate_to', 0, MAX_ENUM_N)
    integer(prefix_to, 'prefix_to', 0, MAX_PREFIX)
    if enumerate_to > max_n:
        raise InputError('enumerate_to cannot exceed max_n')
    values = counts_document(max_n)['sequences']
    p, q, s, a = (values[k] for k in ('A000041', 'A000009', 'A238875', 'A238873'))
    totals = Counter()
    source_lengths = {}
    for seq, source in read_prefixes().items():
        used = min(max_n + 1, len(source['terms']))
        check(values[seq][:used] == source['terms'][:used], 'OEIS prefix mismatch: ' + seq)
        source_lengths[seq] = used
    for n in range(max_n):
        check(s[n + 1] >= s[n], 'subdiagonal monotonicity')
        if n >= 4:
            check(s[n + 1] > s[n], 'strict subdiagonal monotonicity from n=4')
        totals['monotonicity_indices'] += 1
    for n in range(enumerate_to + 1):
        direct = Counter()
        ranks = Counter()
        defects = Counter()
        images = defaultdict(set)
        for lam in partitions(n):
            totals['partitions_enumerated_including_empty'] += 1
            direct['p'] += 1
            direct['q'] += len(set(lam)) == len(lam)
            direct['s'] += all(v <= i for i, v in enumerate(lam, 1))
            direct['a'] += all(v >= i for i, v in enumerate(lam, 1))
            if not lam:
                continue
            k, largest, ones = len(lam), lam[-1], lam.count(1)
            r = largest - k
            defect = max(v - i for i, v in enumerate(lam, 1))
            ranks[r] += 1
            defects[defect] += 1
            dual = conjugate(lam)
            check(conjugate(dual) == lam and rank(dual) == -r, 'conjugation/rank symmetry')
            totals['conjugation_instances'] += 1
            if ones == k:
                try:
                    remove_ones(lam)
                except AllOnesException:
                    pass
                else:
                    raise CheckFailure('all-ones exception was not rejected')
                check(r == 1 - n, 'all-ones rank')
                totals['all_ones_exceptions'] += 1
            else:
                nu = remove_ones(lam)
                check(nu[0] >= 2 and sum(nu) == n, 'injection target and weight')
                check(rank(nu) == r + 2 * ones, 'injection rank formula')
                check(nu not in images[r], 'fixed-rank injection collision')
                images[r].add(nu)
                check(restore_ones(nu, r) == lam, 'fixed-rank inverse')
                totals['fixed_rank_injection_instances'] += 1
            for m in range(1, min(ones, (k - 1) // 2) + 1):
                if (m + 1) * (k - m + 1) <= n:
                    continue
                shift = max(0, r + m)
                check(interior_hypotheses(lam, m, shift), 'interior hypotheses')
                check(defect <= shift, 'deterministic interior lemma')
                totals['interior_lemma_minimal_shift_instances'] += 1
        check((direct['p'], direct['q'], direct['s'], direct['a']) == (p[n], q[n], s[n], a[n]),
              f'independent enumeration/DP mismatch at n={n}')
        totals['independent_count_indices'] += 1
        if n == 0:
            continue
        for r, amount in ranks.items():
            check(amount == ranks[-r], 'rank histogram symmetry')
            if r != 1 - n:
                check(amount <= p[n] - p[n - 1], 'rank atom bound')
                totals['nonexceptional_rank_atom_bounds'] += 1
        check(ranks[1 - n] == 1, 'all-ones rank must be a singleton')
        if n >= 2:
            check(1 <= p[n] - p[n - 1], 'separate all-ones bound for n>=2')
        for shift in range(n + 1):
            lhs = sum(count for d, count in defects.items() if d <= shift)
            rhs = sum(count for r, count in ranks.items() if r <= shift)
            check(lhs <= rhs, 'shifted subdiagonal is a rank subset')
            totals['shifted_rank_subset_comparisons'] += 1
    # Prefix and walk descriptions are independently enumerated.
    for m in range(prefix_to + 1):
        pp = list(prefixes(m))
        check(len(pp) == catalan(m), 'Catalan prefix count')
        totals['catalan_prefixes_enumerated_including_empty'] += len(pp)
        for lam in pp:
            levels = prefix_to_walk(lam)
            check(len(levels) == 2 * m + 1 and levels[0] == levels[-1] == 0
                  and min(levels) >= 0
                  and all(abs(v - u) == 1 for u, v in zip(levels, levels[1:])),
                  'prefix/Dyck-path construction')
            check(sum(lam) <= m * m, 'prefix square weight bound')
        for height in range(1, 9):
            restricted = [lam for lam in pp if all(v <= i + height - 1 for i, v in enumerate(lam, 1))]
            check(len(restricted) == bounded_walk_count(m, height), 'bounded-height exact walk count')
            check(restricted == list(prefixes(m, height)), 'bounded prefix generator')
            for lam in restricted:
                check(max(prefix_to_walk(lam)) <= height, 'bounded-height convention')
                check(sum(lam) <= bounded_weight(m, height), 'bounded-height weight')
            totals['bounded_height_prefix_walk_comparisons'] += 1
    # Independent subset convolution for q and f_M, including zero/negative terms.
    for m in range(1, min(14, max_n) + 1):
        f = distinct_counts(max_n, m)
        subset_weights = Counter({0: 1})
        for part in range(1, m + 1):
            next_weights = Counter(subset_weights)
            for weight, count in subset_weights.items():
                next_weights[weight + part] += count
            subset_weights = next_weights
        for n in range(max_n + 1):
            check(q[n] == sum(count * coefficient(f, n - weight) for weight, count in subset_weights.items()),
                  'small-part subset convolution')
            totals['tail_subset_convolution_indices'] += 1
        for n in range(m + 1, max_n + 1):
            check(f[n] >= 1 and (1 << m) * f[n] >= q[n], 'tail comparison')
            if n < max_n:
                check(f[n + 1] >= f[n], 'tail monotonicity')
            totals['tail_comparison_indices'] += 1
        for n in range(m * m + m + 1, max_n + 1):
            check(a[n] >= catalan(m) * f[n - m * m], 'Catalan finite f-bound')
            check((1 << m) * a[n] >= catalan(m) * q[n - m * m], 'Catalan finite q-bound')
            totals['catalan_finite_lower_bounds'] += 1
        for height in range(3, 9):
            weight = bounded_weight(m, height)
            d = bounded_walk_count(m, height)
            for n in range(weight + m + 1, max_n + 1):
                check(a[n] >= d * f[n - weight], 'bounded-height finite f-bound')
                check((1 << m) * a[n] >= d * q[n - weight], 'bounded-height finite q-bound')
                totals['bounded_height_finite_lower_bounds'] += 1
    # Test actual concatenations, including empty tails and their cutoff inverse.
    for m in range(1, min(prefix_to, 5) + 1):
        pp = list(prefixes(m))
        for n in range(min(max_n, 30) + 1):
            images = set()
            for lam in pp:
                rest = n - sum(lam)
                if rest < 0:
                    continue
                for tail in partitions(rest):
                    if len(set(tail)) != len(tail) or (tail and tail[0] <= m):
                        continue
                    joined = lam + tail
                    check(superdiagonal(joined), 'prefix-tail superdiagonal construction')
                    check(tuple(v for v in joined if v <= m) == lam, 'cutoff inverse')
                    check(joined not in images, 'prefix-tail collision')
                    images.add(joined)
                    totals['prefix_tail_concatenations'] += 1
    return {
        'schema': 'report156-finite-checks-v1', 'status': 'pass',
        'arithmetic': 'exact integer checks; no assertions are disabled by -O',
        'parameters': {'max_n': max_n, 'enumerate_to': enumerate_to, 'prefix_to': prefix_to},
        'coverage': dict(sorted(totals.items())), 'oeis_terms_compared': source_lengths,
        'interior_shift_scope': 'Smallest admissible nonnegative shift for every eligible (partition,m); all larger shifts follow by monotonicity.',
        'all_ones_scope': 'Excluded from the map, checked separately; its atom bound fails only at n=1.',
        'scope': 'Finite checks support implementation and indexing only. They do not prove asymptotic limits, determine an exact superdiagonal growth constant, or certify an asymptotic inverse.'
    }


def threshold_document(value, max_n=MAX_N):
    integer(value, 'value', 1, MAX_THRESHOLD)
    integer(max_n, 'max_n')
    counts = diagonal_counts(max_n, 'sub')
    first = next((n for n, count in enumerate(counts) if count >= value), None)
    return {'schema': 'report156-threshold-v1', 'value': value, 'max_n': max_n,
            'first_n': first, 'reached': first is not None,
            'count_at_first': counts[first] if first is not None else None,
            'previous_count': counts[first - 1] if first is not None and first else None,
            'method': 'exact bounded multiplicity DP, independent of any asymptotic inverse',
            'scope': 'If reached is false, only T(value)>max_n is established.'}


def inverse_model_document(value):
    integer(value, 'value', 3, MAX_THRESHOLD)
    c = math.pi / math.sqrt(6)
    log_y = math.log(value)
    estimate = (log_y + 2 * math.log(log_y) + math.log(12 * math.sqrt(3) / math.pi ** 2)) ** 2 / (4 * c * c)
    return {'schema': 'report156-inverse-model-v1', 'value': value,
            'approximate_initializer': estimate,
            'arithmetic': 'binary floating-point',
            'certified': False,
            'scope': 'Asymptotic initializer only. No computable error bound, certified bracket, or exact integer threshold follows from this number.'}


def _parent_directory(path, trusted):
    if os.name != 'posix' or not hasattr(os, 'O_NOFOLLOW'):
        raise InputError('safe file I/O requires POSIX O_NOFOLLOW')
    if not isinstance(path, (str, os.PathLike)):
        raise InputError('file path must be text or PathLike')
    raw = os.fspath(path)
    if not isinstance(raw, str) or not raw or len(raw) > 4096 or '\x00' in raw or '\\' in raw:
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
        temporary = '.report156-' + secrets.token_hex(16) + '.tmp'
        fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                     0o600, dir_fd=directory)
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
    if not isinstance(text, str) or len(text) > 301 or re.fullmatch(r'0|[1-9][0-9]*', text) is None:
        raise argparse.ArgumentTypeError('expected a canonical nonnegative decimal integer')
    return int(text)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    actions = parser.add_subparsers(dest='action', required=True)
    for name in ('counts', 'verify', 'threshold', 'inverse-model'):
        sub = actions.add_parser(name)
        sub.add_argument('--out', help='fresh .json path in an existing trusted directory; default stdout')
        if name != 'inverse-model':
            sub.add_argument('--max-n', type=cli_integer, default=MAX_N)
        if name == 'verify':
            sub.add_argument('--enumerate-to', type=cli_integer, default=MAX_ENUM_N)
            sub.add_argument('--prefix-to', type=cli_integer, default=MAX_PREFIX)
        if name in ('threshold', 'inverse-model'):
            sub.add_argument('--value', type=cli_integer, required=True)
    args = parser.parse_args(argv)
    try:
        if args.action == 'counts':
            document = counts_document(args.max_n)
        elif args.action == 'verify':
            document = verify(args.max_n, args.enumerate_to, args.prefix_to)
        elif args.action == 'threshold':
            document = threshold_document(args.value, args.max_n)
        else:
            document = inverse_model_document(args.value)
        if args.out is not None:
            write_new_json(args.out, document)
        else:
            sys.stdout.write(encoded_json(document).decode('utf-8'))
    except (InputError, CheckFailure) as exc:
        parser.exit(2, 'error: ' + str(exc) + '\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
