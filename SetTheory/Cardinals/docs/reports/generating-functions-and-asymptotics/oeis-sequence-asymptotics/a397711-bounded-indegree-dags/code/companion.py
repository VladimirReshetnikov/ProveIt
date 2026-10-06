#!/usr/bin/env python3
"""Report157: bounded exact counts/checks for labelled simple DAGs.

Python 3.10+, standard library only. Vertices are [n], loops and parallel edges
are absent, every indegree is at most c, and each DAG is counted once (not once
per topological order). The empty DAG contributes a(0,c)=1. The general theorem
is for each fixed c>=2; c=1 is the separate rooted-forest case.

Examples (run in the directory containing this file):
  python -B companion.py counts --max-n 100 --max-c 5
  python -B companion.py verify
  python -B companion.py threshold --c 2 --value 1000000 --max-n 30
Use --out NEW.json for atomic no-clobber publication. Existing paths are never
replaced. Output parents must exist, belong to the current user, and not be
group/world-writable. Symlink components, special files, path traversal, and
non-JSON output suffixes are refused. File I/O requires POSIX O_NOFOLLOW.

The mathematical checks raise explicitly, including under python -O. Finite
counts do not prove the Airy theorem or certify an asymptotic inverse. This
program intentionally supplies no fitted prefactor or numerical inverse model.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
import json
import math
import os
from pathlib import Path
import re
import secrets
import stat
import sys

MAX_N = 100
MAX_C = 8
DEFAULT_MAX_C = 5
MAX_RATIONAL_N = 25
DEFAULT_RATIONAL_N = 20
MAX_GRAPH_N = 5
MAX_PARKING_N = 5
MAX_PARKING_WORDS = 1_100_000
MAX_PATH_N = 9
MAX_THRESHOLD = 10 ** 1000
MAX_JSON_BYTES = 2 * 1024 * 1024
SOURCE_PATH = Path(__file__).absolute().parent / 'data' / 'oeis_prefixes.json'


class InputError(ValueError):
    """An input, workload, or safe-output precondition was not satisfied."""


class CheckFailure(RuntimeError):
    """An explicit finite mathematical check failed (also under python -O)."""


def integer(value, name, lower=0, upper=MAX_N):
    if type(value) is not int or not lower <= value <= upper:
        raise InputError(f'{name} must be an integer in [{lower}, {upper}]; bool is refused')
    return value


def check(condition, message):
    if not condition:
        raise CheckFailure(message)


def bound_c(c):
    return integer(c, 'c', 1, MAX_C)


def parent_choices(m, c):
    """g_c(m)=sum_{j=0}^c binom(m,j), with binom(m,j)=0 for j>m."""
    integer(m, 'm')
    bound_c(c)
    return sum(math.comb(m, j) for j in range(min(m, c) + 1))


def sink_counts(max_n, c):
    """Inclusion-exclusion on nonempty prescribed sink sets, exact integers."""
    integer(max_n, 'max_n')
    bound_c(c)
    g = [parent_choices(m, c) for m in range(max_n + 1)]
    a = [1]
    for n in range(1, max_n + 1):
        a.append(sum((-1 if k % 2 == 0 else 1) * math.comb(n, k)
                     * g[n - k] ** k * a[n - k] for k in range(1, n + 1)))
    return a


def forest_count(n):
    """Separate c=1 identity, a(n,1)=(n+1)^(n-1) for n>=1."""
    integer(n, 'n')
    return (n + 1) ** (n - 1) if n else 1


def interval_widths(n, c):
    """Positive parking interval widths d_1=1, d_i=sum_{j<c} binom(i-2,j)."""
    integer(n, 'n')
    bound_c(c)
    return ([1] + [sum(math.comb(i - 2, j) for j in range(min(c - 1, i - 2) + 1))
                   for i in range(2, n + 1)]) if n else []


def occupancy_count(n, c):
    """Independent integer DP assigning labelled coordinates to intervals.

    After interval i, at least i coordinates must have been assigned. A state
    records the number assigned, and choosing x of the remaining coordinates
    contributes binom(n-used,x)*d_i^x. This uses neither sinks nor Poisson weights.
    """
    integer(n, 'n', 0, MAX_RATIONAL_N)
    bound_c(c)
    # Obtain widths by differences rather than the Poisson routine's Pascal sum.
    u = [0] + [parent_choices(i - 1, c) for i in range(1, n + 1)]
    state = {0: 1}
    for i in range(1, n + 1):
        d = u[i] - u[i - 1]
        following = {}
        for used, ways in state.items():
            for x in range(max(0, i - used), n - used + 1):
                key = used + x
                following[key] = following.get(key, 0) + ways * math.comb(n - used, x) * d ** x
        state = following
    return state[n]


def poisson_exact(n, c):
    """Return (e^n Z_(n,c), n! prod(d_i) e^n Z_(n,c)) as Fractions.

    At time i the rational area factor is (d_i/d_(i+1))^S_i, before
    X_(i+1)-1 is added. The i=0 factor equals one since S_0=0. After each
    step retain 0<=S_i<=n-i; a larger height cannot return to zero because
    a downward step is at most one. Thus truncation is exact, not numerical.
    The Poisson factor e^-n is removed, leaving step weight 1/X_i!.
    """
    integer(n, 'n', 0, MAX_RATIONAL_N)
    d = interval_widths(n, c)
    factorials = [math.factorial(x) for x in range(n + 1)]
    state = {0: Fraction(1)}
    for i in range(n):
        following = {}
        for height, mass in state.items():
            area = Fraction(d[i - 1], d[i]) ** height if i else Fraction(1)
            for x in range(max(0, 1 - height), n - i - height + 1):
                key = height + x - 1
                following[key] = following.get(key, Fraction(0)) + mass * area / factorials[x]
        state = following
    normalization = math.factorial(n) * math.prod(d)
    return state[0], state[0] * normalization


def brute_dag_counts(n, max_c=DEFAULT_MAX_C):
    """Exhaust all 3^(n choose 2) pair states, then independently test cycles.

    Each unordered pair is absent or oriented in either direction. Opposite
    edges are already impossible in a DAG (a directed 2-cycle), so none are
    omitted. A Kahn deletion test rejects longer directed cycles. No parking
    condition, topological-order generation, or sink recurrence is used here.
    """
    integer(n, 'n', 0, MAX_GRAPH_N)
    bound_c(max_c)
    pairs = list(combinations(range(n), 2))
    histogram = Counter()
    for choices in product(range(3), repeat=len(pairs)):
        indegree = [0] * n
        outgoing = [[] for _ in range(n)]
        for choice, (a, b) in zip(choices, pairs):
            if not choice:
                continue
            if choice == 2:
                a, b = b, a
            outgoing[a].append(b)
            indegree[b] += 1
        maximum = max(indegree, default=0)
        queue = [i for i in range(n) if indegree[i] == 0]
        deleted = 0
        while queue:
            a = queue.pop()
            deleted += 1
            for b in outgoing[a]:
                indegree[b] -= 1
                if indegree[b] == 0:
                    queue.append(b)
        if deleted == n:
            histogram[maximum] += 1
    return {c: sum(number for degree, number in histogram.items() if degree <= c)
            for c in range(1, max_c + 1)}


def parking_word_count(n, c):
    """Direct preference-word enumeration, independent of both DPs."""
    integer(n, 'n', 0, MAX_PARKING_N)
    bound_c(c)
    if n == 0:
        return 1
    bounds = [parent_choices(i, c) for i in range(n)]
    if bounds[-1] ** n > MAX_PARKING_WORDS:
        raise InputError('parking-word workload exceeds the explicit word cap')
    return sum(all(value <= bound for value, bound in zip(sorted(word), bounds))
               for word in product(range(1, bounds[-1] + 1), repeat=n))


def excursion_occupancies(n):
    """Small direct compositions with nonnegative partial sums of x_i-1."""
    integer(n, 'n', 0, MAX_PATH_N)
    def extend(remaining_steps, remaining_sum, height, selected):
        if remaining_steps == 0:
            if remaining_sum == 0 and height == 0:
                yield selected
            return
        for x in range(max(0, 1 - height), remaining_sum + 1):
            following = height + x - 1
            if following <= remaining_steps - 1:
                yield from extend(remaining_steps - 1, remaining_sum - x, following, selected + (x,))
    return extend(n, n, 0, ())


def pathwise_checks(n, c):
    """Check summation by parts in its exact multiplicative rational form."""
    integer(n, 'n', 0, MAX_PATH_N)
    d = interval_widths(n, c)
    seen = 0
    for path in excursion_occupancies(n):
        lhs = Fraction(1)
        rhs = Fraction(1)
        height = 0
        for i, x in enumerate(path):
            lhs *= Fraction(d[i]) ** (x - 1)
            if i:
                rhs *= Fraction(d[i - 1], d[i]) ** height
            height += x - 1
            check(height >= 0, 'direct excursion became negative')
        check(height == 0 and lhs == rhs, f'pathwise Poisson factor mismatch at n={n}, c={c}')
        seen += 1
    return seen


def counts_document(max_n=MAX_N, max_c=DEFAULT_MAX_C):
    integer(max_n, 'max_n')
    bound_c(max_c)
    return {
        'schema': 'report157-counts-v1',
        'arithmetic': 'exact integers',
        'index_start': 0, 'max_n': max_n, 'max_c': max_c,
        'convention': 'Simple DAGs on labelled vertices [n], maximum indegree c; a(0,c)=1; no topological-order multiplicity.',
        'algorithm': 'inclusion-exclusion over prescribed nonempty sink sets',
        'counts_by_c': {str(c): sink_counts(max_n, c) for c in range(1, max_c + 1)},
        'scope': 'Finite exact values only. The theorem concerns each fixed c>=2; c=1 is checked separately. No prefactor, asymptotic error bound, or certified asymptotic inverse is inferred.'
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
    """Read a bounded numerical source extract as data; never execute it."""
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
        if type(payload) is not dict or payload.get('schema') != 'report157-oeis-prefixes-v1':
            raise InputError('unexpected prefix source schema')
        sources = payload.get('sequences')
        if type(sources) is not dict or set(sources) != {'A397711'}:
            raise InputError('prefix source must contain exactly A397711')
        source = sources['A397711']
        if type(source) is not dict or source.get('source_url') != 'https://oeis.org/A397711':
            raise InputError('unexpected sequence source URL')
        integer(source.get('offset'), 'offset', 0, 0)
        integer(source.get('c'), 'source indegree bound', 2, 2)
        values = source.get('terms')
        if type(values) is not list or not 1 <= len(values) <= MAX_N + 1:
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


def verify(max_n=MAX_N, max_c=DEFAULT_MAX_C, rational_to=DEFAULT_RATIONAL_N,
           enumerate_to=MAX_GRAPH_N, parking_to=MAX_PARKING_N, path_to=MAX_PATH_N):
    """Deterministic explicit checks, with individually bounded workloads."""
    integer(max_n, 'max_n')
    bound_c(max_c)
    for name, value, limit in (('rational_to', rational_to, MAX_RATIONAL_N),
                               ('enumerate_to', enumerate_to, MAX_GRAPH_N),
                               ('parking_to', parking_to, MAX_PARKING_N),
                               ('path_to', path_to, MAX_PATH_N)):
        integer(value, name, 0, limit)
        if value > max_n:
            raise InputError(name + ' cannot exceed max_n')
    counts = counts_document(max_n, max_c)['counts_by_c']
    totals = Counter()
    for c in range(1, max_c + 1):
        seq = counts[str(c)]
        for n, value in enumerate(seq):
            check(value >= 1, f'nonpositive count at n={n}, c={c}')
            if n:
                check(value >= n * seq[n - 1], 'labelled-sink extension lower bound')
                check(value <= parent_choices(n - 1, c) ** n, 'unrestricted parent-set upper bound')
                totals['extension_and_parent_set_bounds'] += 1
            if c > 1:
                check(value >= counts[str(c - 1)][n], 'monotonicity in indegree bound')
                totals['indegree_monotonicity_indices'] += 1
    for n in range(max_n + 1):
        check(counts['1'][n] == forest_count(n), 'c=1 rooted-forest formula')
        totals['forest_formula_indices'] += 1
    compared = {}
    for seq, source in read_prefixes().items():
        used = min(max_n + 1, len(source['terms']))
        # Compare even if max_c=1: this is an independent c=2 source check.
        c2 = counts.get('2', sink_counts(max_n, 2))
        check(c2[:used] == source['terms'][:used], 'OEIS prefix mismatch: ' + seq)
        compared[seq] = used
    graphs = []
    for n in range(enumerate_to + 1):
        actual = brute_dag_counts(n, max_c)
        for c, value in actual.items():
            check(value == counts[str(c)][n], f'direct DAG mismatch at n={n}, c={c}')
            totals['direct_graph_count_comparisons'] += 1
        totals['graph_pair_state_assignments'] += 3 ** math.comb(n, 2)
        graphs.append({'n': n, 'counts_by_c': {str(c): v for c, v in actual.items()}})
    parking = []
    poisson = []
    for c in range(1, max_c + 1):
        for n in range(parking_to + 1):
            value = parking_word_count(n, c)
            check(value == counts[str(c)][n], f'direct parking mismatch at n={n}, c={c}')
            totals['parking_word_count_comparisons'] += 1
            totals['parking_words_enumerated'] += parent_choices(n - 1, c) ** n if n else 1
            parking.append({'c': c, 'n': n, 'count': value})
        for n in range(rational_to + 1):
            en_z, from_poisson = poisson_exact(n, c)
            from_occupancy = occupancy_count(n, c)
            check(from_poisson.denominator == 1 and from_poisson.numerator == counts[str(c)][n],
                  f'exact Poisson mismatch at n={n}, c={c}')
            check(from_occupancy == counts[str(c)][n], f'occupancy mismatch at n={n}, c={c}')
            totals['occupancy_poisson_sink_comparisons'] += 1
            poisson.append({'c': c, 'n': n, 'e_to_n_Z_numerator': en_z.numerator,
                            'e_to_n_Z_denominator': en_z.denominator, 'count': from_occupancy})
        for n in range(path_to + 1):
            paths = pathwise_checks(n, c)
            check(paths == math.comb(2 * n, n) // (n + 1), 'excursion composition Catalan count')
            totals['pathwise_summation_by_parts_instances'] += paths
            totals['pathwise_composition_count_comparisons'] += 1
    return {
        'schema': 'report157-finite-checks-v1', 'status': 'pass',
        'arithmetic': 'exact integers and rational numbers; checks remain active under -O',
        'parameters': {'max_n': max_n, 'max_c': max_c, 'rational_to': rational_to,
                       'enumerate_to': enumerate_to, 'parking_to': parking_to, 'path_to': path_to},
        'coverage': dict(sorted(totals.items())), 'oeis_terms_compared': compared,
        'direct_graph_counts': graphs, 'direct_parking_counts': parking,
        'occupancy_and_poisson': poisson,
        'normalization': 'a(n,c)=n! prod(d_i) e^n Z_(n,c); area is charged at left endpoints; n=0 uses empty products.',
        'scope': 'Finite checks validate implementation and indexing only. They do not prove the asymptotic theorem, a prefactor, an asymptotic error estimate, or certified asymptotic inversion.'
    }


def threshold_document(value, c=2, max_n=MAX_N):
    """Exact N_c(value)=min{n>=1:a(n,c)>=value}, searched only to max_n."""
    integer(value, 'value', 1, MAX_THRESHOLD)
    bound_c(c)
    integer(max_n, 'max_n', 1, MAX_N)
    counts = sink_counts(max_n, c)
    first = next((n for n in range(1, max_n + 1) if counts[n] >= value), None)
    return {
        'schema': 'report157-threshold-v1', 'value': value, 'c': c, 'max_n': max_n,
        'search_starts_at': 1, 'first_n': first, 'reached': first is not None,
        'count_at_first': counts[first] if first is not None else None,
        'previous_count': counts[first - 1] if first is not None and first > 1 else None,
        'last_count_searched': counts[-1],
        'method': 'exact bounded sink recurrence; no asymptotic approximation is used',
        'scope': 'If reached is false, only N_c(value)>max_n is established; no larger threshold is guessed.'
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
        candidate = '.report157-' + secrets.token_hex(16) + '.tmp'
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


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    actions = parser.add_subparsers(dest='action', required=True)
    for name in ('counts', 'verify', 'threshold'):
        sub = actions.add_parser(name)
        sub.add_argument('--out', help='fresh .json path in an existing trusted directory; default stdout')
        sub.add_argument('--max-n', type=cli_integer, default=MAX_N)
        if name in ('counts', 'verify'):
            sub.add_argument('--max-c', type=cli_integer, default=DEFAULT_MAX_C)
        if name == 'verify':
            sub.add_argument('--rational-to', type=cli_integer, default=None)
            sub.add_argument('--enumerate-to', type=cli_integer, default=None)
            sub.add_argument('--parking-to', type=cli_integer, default=None)
            sub.add_argument('--path-to', type=cli_integer, default=None)
        if name == 'threshold':
            sub.add_argument('--c', type=cli_integer, default=2)
            sub.add_argument('--value', type=cli_integer, required=True)
    args = parser.parse_args(argv)
    try:
        if args.action == 'counts':
            document = counts_document(args.max_n, args.max_c)
        elif args.action == 'verify':
            limits = ((args.rational_to, DEFAULT_RATIONAL_N), (args.enumerate_to, MAX_GRAPH_N),
                      (args.parking_to, MAX_PARKING_N), (args.path_to, MAX_PATH_N))
            chosen = [min(args.max_n, default) if supplied is None else supplied for supplied, default in limits]
            document = verify(args.max_n, args.max_c, *chosen)
        else:
            document = threshold_document(args.value, args.c, args.max_n)
        if args.out is not None:
            write_new_json(args.out, document)
        else:
            sys.stdout.write(encoded_json(document).decode('utf-8'))
    except (InputError, CheckFailure) as exc:
        parser.exit(2, 'error: ' + str(exc) + '\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
