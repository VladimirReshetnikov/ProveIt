#!/usr/bin/env python3
"""Report158: exact bounded checks for increasing superdiagonal partitions.

Python 3.10+, standard library only. Parts are weakly increasing positive
integers, lambda_i >= i, and A(0)=1. All finite decisions use integers or
fractions.Fraction; no floating-point test is used as mathematical evidence.

  python -B companion.py counts --max-n 200
  python -B companion.py verify
  python -B companion.py threshold --value 1000000 --max-n 200

Use --out NEW.json for atomic no-clobber output. Its existing parent must be
owned by the current user and not group/world-writable. Symlink components,
existing targets, dot/parent traversal, and non-JSON suffixes are refused.
The POSIX I/O contract assumes trusted ancestors and nonadversarial same-user
concurrency; it does not protect against malicious code running as this user.
Finite checks validate definitions and inequalities, not an asymptotic theorem,
a multiplicative equivalent, an optimal error order, or an asymptotic inverse.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import json
import math
import os
from pathlib import Path
import re
import secrets
import stat
import sys

MAX_N = 200
MAX_ENUMERATE = 40
MAX_PREFIX = 10
MAX_SURVIVAL = 30
MAX_WEIGHTED_J = 30
MAX_RATIONAL_DENOMINATOR = 100
MAX_THRESHOLD = 10 ** 1000
MAX_JSON_BYTES = 2 * 1024 * 1024
SOURCE_PATH = Path(__file__).absolute().parent / 'data' / 'oeis_prefixes.json'


class InputError(ValueError):
    """An input, workload, or safe-file-I/O precondition is not satisfied."""


class CheckFailure(RuntimeError):
    """A finite mathematical check failed, including under python -O."""


def integer(value, name, lower=0, upper=MAX_N):
    if type(value) is not int or not lower <= value <= upper:
        raise InputError(f'{name} must be an integer in [{lower}, {upper}]; bool is refused')
    return value


def check(condition, message):
    if not condition:
        raise CheckFailure(message)


def probability(value, name='probability'):
    """Require an actual bounded Fraction, not a float or coerced integer."""
    if type(value) is not Fraction or not 0 < value < 1 or value.denominator > MAX_RATIONAL_DENOMINATOR:
        raise InputError(f'{name} must be a Fraction strictly between 0 and 1, with denominator <= {MAX_RATIONAL_DENOMINATOR}')
    return value


def counts(max_n=MAX_N, cutoff=0):
    """Exact fresh-layer multiplicity DP, with no in-place coin-change step.

    After value v the state (weight, length) counts partitions with parts in
    (cutoff,v], subject to C_j <= j-cutoff for cutoff < j <= v. A fresh layer
    chooses the multiplicity z of v once, admitting length+z <= v-cutoff.
    Later parts cannot alter earlier cumulative counts. The length bound K
    follows from weight >= cutoff*K + K*(K+1)/2. No omitted part >max_n can
    contribute to the requested coefficients. cutoff=0 gives A(n).
    """
    integer(max_n, 'max_n')
    integer(cutoff, 'cutoff')
    base = 2 * cutoff + 1
    length_bound = (math.isqrt(base * base + 8 * max_n) - base) // 2
    state = {(0, 0): 1}
    for value in range(cutoff + 1, max_n + 1):
        following = {}
        for (weight, length), number in state.items():
            largest_z = min(value - cutoff - length, length_bound - length,
                            (max_n - weight) // value)
            for z in range(largest_z + 1):
                key = weight + value * z, length + z
                following[key] = following.get(key, 0) + number
        state = following
    result = [0] * (max_n + 1)
    for (weight, _length), number in state.items():
        result[weight] += number
    return result


def partitions(n):
    """Independent ascending-list enumeration of every integer partition of n."""
    integer(n, 'n', 0, MAX_ENUMERATE)
    def extend(remaining, minimum, selected):
        if remaining == 0:
            yield selected
            return
        for value in range(minimum, remaining + 1):
            yield from extend(remaining - value, value, selected + (value,))
    return extend(n, 1, ())


def _partition(parts, max_weight=MAX_N):
    if type(parts) not in (tuple, list) or len(parts) > MAX_N:
        raise InputError('partition must be a bounded tuple or list')
    for part in parts:
        integer(part, 'part', 1, MAX_N)
    if any(a > b for a, b in zip(parts, parts[1:])) or sum(parts) > max_weight:
        raise InputError('partition must be weakly increasing with bounded total weight')
    return tuple(parts)


def indexed_constraint(parts):
    parts = _partition(parts)
    return all(part >= i for i, part in enumerate(parts, 1))


def cumulative_constraint(parts):
    parts = _partition(parts)
    multiplicities = Counter(parts)
    cumulative = 0
    for value in range(1, parts[-1] + 1 if parts else 1):
        cumulative += multiplicities[value]
        if cumulative > value:
            return False
    return True


def monotonicity_image(parts):
    """Raise one largest part; the image has a unique largest part."""
    parts = _partition(parts, MAX_N - 1)
    if not indexed_constraint(parts):
        raise InputError('injection requires an admissible partition')
    return parts[:-1] + (parts[-1] + 1,) if parts else (1,)


def prefixes(M, h):
    """Enumerate i <= lambda_i <= min(M,i+h-1), with exactly M parts."""
    integer(M, 'M', 0, MAX_PREFIX)
    integer(h, 'h', 1, MAX_PREFIX)
    def extend(i, previous, selected):
        if i > M:
            yield selected
            return
        for value in range(max(i, previous), min(M, i + h - 1) + 1):
            yield from extend(i + 1, value, selected + (value,))
    return extend(1, 1, ())


def prefix_weight_bound(M, h):
    integer(M, 'M', 0, MAX_PREFIX)
    integer(h, 'h', 1, MAX_PREFIX)
    return M * (M + 1) // 2 + (h - 1) * M


def dyck_count(M, h):
    """(T_h^(2M))_(0,0), via exact nearest-neighbor walk transfer."""
    integer(M, 'M', 0, MAX_PREFIX)
    integer(h, 'h', 1, MAX_PREFIX)
    heights = [1] + [0] * h
    for _ in range(2 * M):
        following = [0] * (h + 1)
        for level, number in enumerate(heights):
            if level:
                following[level - 1] += number
            if level < h:
                following[level + 1] += number
        heights = following
    return heights[0]


def prefix_to_dyck(parts, h):
    """Reverse complement, then put north step j at x=mu_j-1."""
    parts = _partition(parts)
    M = integer(len(parts), 'M', 0, MAX_PREFIX)
    integer(h, 'h', 1, MAX_PREFIX)
    if any(not i <= value <= min(M, i + h - 1) for i, value in enumerate(parts, 1)):
        raise InputError('partition is outside the specified prefix strip')
    mu = [M + 1 - value for value in reversed(parts)]
    steps = []
    x = 0
    for value in mu:
        while x < value - 1:
            steps.append(-1)
            x += 1
        steps.append(1)
    steps.extend([-1] * (M - x))
    return tuple(steps)


def dyck_to_prefix(steps, h):
    """Inverse path map; reject paths outside height [0,h]."""
    integer(h, 'h', 1, MAX_PREFIX)
    if type(steps) not in (tuple, list) or len(steps) > 2 * MAX_PREFIX or len(steps) % 2:
        raise InputError('Dyck steps must be a bounded even-length tuple or list')
    level = x = 0
    mu = []
    for step in steps:
        if type(step) is not int or step not in (-1, 1):
            raise InputError('Dyck steps must be exact integers -1 or 1')
        level += step
        if not 0 <= level <= h:
            raise InputError('Dyck path leaves the specified strip')
        if step == 1:
            mu.append(x + 1)
        else:
            x += 1
    if level:
        raise InputError('Dyck path does not return to zero')
    M = len(steps) // 2
    return tuple(M + 1 - value for value in reversed(mu))


def survival(p, horizon):
    """Exact P(sum_(i<=j) Z_i <= j, 1<=j<=horizon), geometric p.

    A state records deficit j-sum Z_i. A surviving next transition has
    0<=z<=deficit+1, so every included geometric probability is exact and
    every omitted transition is already outside the event, not a tail cutoff.
    """
    probability(p, 'p')
    integer(horizon, 'horizon', 0, MAX_SURVIVAL)
    state = {0: Fraction(1)}
    for _ in range(horizon):
        following = {}
        for deficit, mass in state.items():
            for z in range(deficit + 2):
                key = deficit + 1 - z
                following[key] = following.get(key, Fraction(0)) + mass * (1 - p) * p ** z
        state = following
    return sum(state.values(), Fraction(0))


def finite_weighted(q, largest_part, cutoff=0):
    """Finite rational sum for parts in (cutoff,J], C_v<=v-cutoff.

    The state records length. Multiplicity z contributes q^(v*z); admissible
    cumulative length is at most v-cutoff. Thus all partitions in this finite
    generating polynomial are included, with maximum length J-cutoff.
    """
    probability(q, 'q')
    integer(largest_part, 'largest_part', 0, MAX_WEIGHTED_J)
    integer(cutoff, 'cutoff', 0, largest_part)
    state = {0: Fraction(1)}
    for value in range(cutoff + 1, largest_part + 1):
        following = {}
        for length, weight in state.items():
            for z in range(value - cutoff - length + 1):
                key = length + z
                following[key] = following.get(key, Fraction(0)) + weight * q ** (value * z)
        state = following
    return sum(state.values(), Fraction(0))


def tail_product(q, largest_part, cutoff=0):
    probability(q, 'q')
    integer(largest_part, 'largest_part', 0, MAX_WEIGHTED_J)
    integer(cutoff, 'cutoff', 0, largest_part)
    result = Fraction(1)
    for value in range(cutoff + 1, largest_part + 1):
        result /= 1 - q ** value
    return result


def tilt_cutoff(q):
    """Largest M with q^M>=1/2; equality is included without logarithms."""
    probability(q, 'q')
    M = 0
    while M < MAX_WEIGHTED_J and q ** (M + 1) >= Fraction(1, 2):
        M += 1
    if q ** (M + 1) >= Fraction(1, 2):
        raise InputError('tilt cutoff exceeds bounded weighted workload')
    return M


def counts_document(max_n=MAX_N):
    integer(max_n, 'max_n')
    return {
        'schema': 'report158-counts-v1', 'arithmetic': 'exact integers',
        'sequence': 'A238873', 'index_start': 0, 'max_n': max_n,
        'convention': 'Weakly increasing positive parts lambda_i >= i; A(0)=1.',
        'algorithm': 'fresh-layer multiplicity DP with cumulative-count cap',
        'counts': counts(max_n),
        'scope': 'Finite exact counts only; no asymptotic assertion is inferred.'
    }


def _unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise InputError('duplicate JSON key: ' + key)
        result[key] = value
    return result


def _no_noninteger(token):
    raise InputError('noninteger or nonfinite source JSON number is refused')


def _source_integer(token):
    if len(token) > 102:
        raise InputError('source integer token is too long')
    return int(token)


def read_prefixes(path=SOURCE_PATH):
    """Read only a bounded attributed numerical extract; never execute it."""
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
        if type(payload) is not dict or payload.get('schema') != 'report158-oeis-prefixes-v1':
            raise InputError('unexpected prefix source schema')
        sources = payload.get('sequences')
        if type(sources) is not dict or set(sources) != {'A238873'}:
            raise InputError('prefix source must contain exactly A238873')
        source = sources['A238873']
        if type(source) is not dict or source.get('source_url') != 'https://oeis.org/A238873':
            raise InputError('unexpected sequence source URL')
        integer(source.get('offset'), 'offset', 0, 0)
        terms = source.get('terms')
        if type(terms) is not list or not 1 <= len(terms) <= MAX_N + 1:
            raise InputError('invalid numerical prefix length')
        for term in terms:
            integer(term, 'prefix term', 0, 10 ** 100)
        return sources
    except (OSError, UnicodeError, json.JSONDecodeError, RecursionError) as exc:
        raise InputError('cannot read prefix source: ' + str(exc)) from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)
        if directory is not None:
            os.close(directory)


def verify(max_n=MAX_N, enumerate_to=MAX_ENUMERATE, prefix_to=MAX_PREFIX,
           height_to=MAX_PREFIX, survival_to=MAX_SURVIVAL):
    """Replay bounded exact checks; every comparison survives optimization."""
    integer(max_n, 'max_n')
    integer(enumerate_to, 'enumerate_to', 0, MAX_ENUMERATE)
    integer(prefix_to, 'prefix_to', 0, MAX_PREFIX)
    integer(height_to, 'height_to', 1, MAX_PREFIX)
    integer(survival_to, 'survival_to', 0, MAX_SURVIVAL)
    if enumerate_to > max_n:
        raise InputError('enumerate_to cannot exceed max_n')
    a = counts(max_n)
    totals = Counter({name: 0 for name in (
        'constraint_equivalence_partitions', 'direct_enumeration_indices',
        'monotonicity_injection_images', 'count_monotonicity_indices',
        'prefix_count_comparisons', 'prefix_weight_and_bijection_instances',
        'prefix_tail_coefficient_inequalities', 'rational_survival_horizons',
        'rational_martingale_normalizations', 'rational_tilted_upper_inequalities',
        'rational_tail_product_lower_inequalities', 'rational_prefix_tail_inequalities')})
    for n in range(1, max_n + 1):
        check(a[n] >= a[n - 1] >= 1, f'count monotonicity at n={n}')
        totals['count_monotonicity_indices'] += 1
    source = read_prefixes()['A238873']
    used = min(max_n + 1, len(source['terms']))
    check(a[:used] == source['terms'][:used], 'OEIS A238873 prefix mismatch')
    for n in range(enumerate_to + 1):
        images = set()
        valid_count = 0
        for parts in partitions(n):
            indexed = indexed_constraint(parts)
            check(indexed == cumulative_constraint(parts), f'constraint equivalence: {parts}')
            totals['constraint_equivalence_partitions'] += 1
            if not indexed:
                continue
            valid_count += 1
            mapped = monotonicity_image(parts)
            check(sum(mapped) == n + 1 and indexed_constraint(mapped), 'invalid monotonicity image')
            check(mapped not in images, 'monotonicity injection collision')
            check(len(mapped) == 1 or mapped[-1] > mapped[-2], 'image largest part is not unique')
            recovered = mapped[:-1] + (mapped[-1] - 1,) if n else ()
            check(recovered == parts, 'monotonicity inverse mismatch')
            images.add(mapped)
            totals['monotonicity_injection_images'] += 1
        check(valid_count == a[n], f'direct partition count mismatch at n={n}')
        totals['direct_enumeration_indices'] += 1
    for M in range(1, prefix_to + 1):
        tail = counts(max_n, M)
        for h in range(1, height_to + 1):
            histogram = Counter()
            paths = set()
            bound = prefix_weight_bound(M, h)
            for parts in prefixes(M, h):
                weight = sum(parts)
                check(weight <= bound, f'prefix weight at M={M}, h={h}')
                check(indexed_constraint(parts), 'inadmissible prefix')
                steps = prefix_to_dyck(parts, h)
                check(dyck_to_prefix(steps, h) == parts, 'prefix-Dyck inverse mismatch')
                check(steps not in paths, 'prefix-Dyck collision')
                paths.add(steps)
                histogram[weight] += 1
                totals['prefix_weight_and_bijection_instances'] += 1
            check(sum(histogram.values()) == dyck_count(M, h), 'Dyck transfer count mismatch')
            totals['prefix_count_comparisons'] += 1
            for n in range(max_n + 1):
                coefficient = sum(number * tail[n - weight]
                                  for weight, number in histogram.items() if weight <= n)
                check(coefficient <= a[n], f'prefix-tail coefficient inequality at {M},{h},{n}')
                totals['prefix_tail_coefficient_inequalities'] += 1
    survival_rows = []
    for p in (Fraction(1, 4), Fraction(1, 3), Fraction(49, 100)):
        bound = 1 - 2 * p
        previous = Fraction(1)
        for horizon in range(survival_to + 1):
            actual = survival(p, horizon)
            check(bound <= actual <= previous, f'finite survival bound at {p},{horizon}')
            previous = actual
            totals['rational_survival_horizons'] += 1
        r = (1 - p) / p
        root = (1 - p) / (r * (1 - p * r))
        check(root == 1, 'geometric martingale normalization')
        totals['rational_martingale_normalizations'] += 1
        survival_rows.append({'p': str(p), 'horizon': survival_to,
                              'finite_survival': str(previous), 'lower_bound': str(bound),
                              'martingale_root': str(r), 'root_mgf': str(root)})
    weighted_rows = []
    for q in (Fraction(1, 2), Fraction(2, 3), Fraction(3, 4), Fraction(9, 10)):
        M = tilt_cutoff(q)
        J = M + 10
        product = tail_product(q, J, M)
        full = finite_weighted(q, J)
        upper = 4 ** M * q ** (M * (M + 1) // 2) * product
        check(full <= upper, 'finite exponential-tilt upper bound')
        totals['rational_tilted_upper_inequalities'] += 1
        tail = finite_weighted(q, J, M)
        delta = 1 - 2 * q ** (M + 1)
        check(tail >= delta * product, 'finite tail product lower bound')
        totals['rational_tail_product_lower_inequalities'] += 1
        # These are finite versions of the full prefix-tail lower inequality.
        # Use M>=1 here; each chosen q has a positive tilt cutoff.
        for h in range(1, height_to + 1):
            prefix_weight = sum((q ** sum(parts) for parts in prefixes(M, h)), Fraction(0))
            coarse_weight = dyck_count(M, h) * q ** prefix_weight_bound(M, h)
            check(prefix_weight >= coarse_weight, 'rational prefix weight lower bound')
            check(full >= prefix_weight * tail >= coarse_weight * delta * product,
                  'finite prefix-tail generating inequality')
            totals['rational_prefix_tail_inequalities'] += 1
        weighted_rows.append({'q': str(q), 'cutoff_M': M, 'largest_part_J': J,
                              'finite_full': str(full), 'tilted_upper': str(upper),
                              'finite_tail': str(tail), 'tail_product': str(product),
                              'finite_tail_survival': str(tail / product), 'delta': str(delta)})
    return {
        'schema': 'report158-finite-checks-v1', 'status': 'pass',
        'arithmetic': 'exact integers and rational strings; all checks active under -O',
        'parameters': {'max_n': max_n, 'enumerate_to': enumerate_to, 'prefix_to': prefix_to,
                       'height_to': height_to, 'survival_to': survival_to},
        'coverage': dict(sorted(totals.items())), 'oeis_terms_compared': {'A238873': used},
        'rational_survival': survival_rows, 'rational_weighted_products': weighted_rows,
        'selected_counts': {str(n): a[n] for n in (0, 1, 2, 8, 13, 20, 40, 60, 100, 150, 200) if n <= max_n},
        'scope': 'Finite checks validate definitions, indexing, exact counts, and finite inequalities only. They do not prove an asymptotic theorem, an infinite-horizon probability bound, a multiplicative equivalent, a sharp second term, an optimal error order, or an asymptotic inverse.'
    }


def threshold_document(value, max_n=MAX_N):
    """Exact min{n>=0:A(n)>=value}, searched only through max_n."""
    integer(value, 'value', 1, MAX_THRESHOLD)
    integer(max_n, 'max_n')
    sequence = counts(max_n)
    first = next((n for n, count in enumerate(sequence) if count >= value), None)
    return {
        'schema': 'report158-threshold-v1', 'value': value, 'max_n': max_n,
        'search_starts_at': 0, 'first_n': first, 'reached': first is not None,
        'count_at_first': sequence[first] if first is not None else None,
        'previous_count': sequence[first - 1] if first is not None and first > 0 else None,
        'last_count_searched': sequence[-1],
        'method': 'exact bounded multiplicity DP; no asymptotic approximation',
        'scope': 'An unreached target establishes only that its threshold exceeds max_n; no larger index is guessed.'
    }


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
    """Exclusively hard-link a fully written private file into a pinned parent.

    Existing files, symlinks, directories, and special targets are never replaced.
    A failure after publication may leave a complete output; inspect rather than
    blindly retrying or deleting it. Trusted ancestors and nonadversarial same-user
    concurrency are assumptions; malicious same-UID interference is not covered.
    """
    data = encoded_json(document)
    directory = descriptor = None
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
        candidate = '.report158-' + secrets.token_hex(16) + '.tmp'
        descriptor = os.open(candidate, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                             0o600, dir_fd=directory)
        temporary = candidate
        with os.fdopen(descriptor, 'wb') as stream:
            descriptor = None
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
        if descriptor is not None:
            os.close(descriptor)
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


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter,
                                     allow_abbrev=False)
    commands = parser.add_subparsers(dest='action', required=True)
    for name in ('counts', 'verify', 'threshold'):
        sub = commands.add_parser(name, allow_abbrev=False)
        sub.add_argument('--max-n', type=cli_integer, default=MAX_N)
        sub.add_argument('--out', help='fresh .json path in an existing trusted parent; default stdout')
        if name == 'verify':
            sub.add_argument('--enumerate-to', type=cli_integer, default=None)
            sub.add_argument('--prefix-to', type=cli_integer, default=MAX_PREFIX)
            sub.add_argument('--height-to', type=cli_integer, default=MAX_PREFIX)
            sub.add_argument('--survival-to', type=cli_integer, default=MAX_SURVIVAL)
        elif name == 'threshold':
            sub.add_argument('--value', type=cli_integer, required=True)
    args = parser.parse_args(argv)
    try:
        if args.action == 'counts':
            document = counts_document(args.max_n)
        elif args.action == 'verify':
            enumeration = min(args.max_n, MAX_ENUMERATE) if args.enumerate_to is None else args.enumerate_to
            document = verify(args.max_n, enumeration, args.prefix_to, args.height_to, args.survival_to)
        else:
            document = threshold_document(args.value, args.max_n)
        if args.out is None:
            sys.stdout.write(encoded_json(document).decode('utf-8'))
        else:
            write_new_json(args.out, document)
    except (InputError, CheckFailure) as exc:
        parser.exit(2, 'error: ' + str(exc) + '\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
