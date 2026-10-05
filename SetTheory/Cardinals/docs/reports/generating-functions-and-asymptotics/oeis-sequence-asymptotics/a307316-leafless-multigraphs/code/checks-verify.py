#!/usr/bin/env python3
"""Report131: exact finite checks only, never a certificate of an asymptotic theorem.

Python 3.10+ standard library. Run normally and with ``python -O``. All validation
uses explicit exceptions, never the assert statement. No network, input mutation,
floating point, graph library, or symbolic-algebra package is used.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
import itertools
import json
import math
import os
from pathlib import Path
import shutil
import sys
import tempfile

FIXTURE_SHA256 = "edb1f99589849de10f6e30269ddb6108507ce3b70c656c76adfc7ee598fb9c5f"
SOURCE_NAMES = frozenset({"b307316.txt", "b307317.txt"})


class VerificationError(RuntimeError):
    """A required exact equality, range, schema, or integrity condition failed."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def integer(value):
    return type(value) is int


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def validate_output_destination(destination, package_root):
    """Reject package writes, replacement writes, and symbolic path traversal."""
    destination = Path(destination)
    require('..' not in destination.parts, 'output path must not contain parent traversal')
    absolute = destination if destination.is_absolute() else Path.cwd() / destination
    package_root = Path(package_root).resolve()
    # Inspect lexical components before resolving, including dangling symlinks.
    for component in [*reversed(absolute.parents), absolute]:
        require(not component.is_symlink(), 'output path or ancestor is a symlink')
    resolved = absolute.resolve(strict=False)
    require(resolved != package_root and package_root not in resolved.parents,
        'output must be strictly outside the entire package root')
    require(not absolute.exists(), 'output destination already exists; refusing to overwrite')
    require(absolute.parent.is_dir(), 'output parent directory does not exist')
    require(all(ancestor.is_dir() for ancestor in absolute.parents),
        'output ancestor is not a directory')
    return resolved


def write_exclusive_output(destination, package_root, text):
    """Revalidate, traverse directories without symlinks, then create exclusively.

    Directory file descriptors and O_NOFOLLOW avoid a symlink substitution between
    validation and creation. O_EXCL prevents overwriting a concurrently created file.
    """
    destination = validate_output_destination(destination, package_root)
    require(hasattr(os, 'O_NOFOLLOW') and hasattr(os, 'O_DIRECTORY'),
        'safe file output requires POSIX O_NOFOLLOW and O_DIRECTORY')
    directory_fd = None
    try:
        directory_fd = os.open(destination.anchor, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        for part in destination.parts[1:-1]:
            next_fd = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=directory_fd)
            os.close(directory_fd)
            directory_fd = next_fd
        output_fd = os.open(destination.name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
            0o600, dir_fd=directory_fd)
        with os.fdopen(output_fd, 'w', encoding='utf-8') as output:
            output.write(text)
    except OSError as error:
        raise VerificationError(f'exclusive output creation failed: {error}') from error
    finally:
        if directory_fd is not None:
            os.close(directory_fd)


def parse_bfile(text):
    result = {}
    for line_number, line in enumerate(text.splitlines(), 1):
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        fields = line.split()
        require(len(fields) == 2, f"b-file line {line_number}: expected two columns")
        try:
            index, value = map(int, fields)
        except ValueError as error:
            raise VerificationError(f"b-file line {line_number}: noninteger") from error
        require(index >= 0 and value >= 0, "b-file indices and counts must be nonnegative")
        require(index not in result, "duplicate b-file index")
        result[index] = value
    require(bool(result), "empty b-file")
    require(sorted(result) == list(range(max(result) + 1)), "noncontiguous b-file indices")
    return [result[i] for i in range(len(result))]


def verify_inputs(root):
    fixture_path = root / 'fixtures.json'
    require(fixture_path.is_file() and not fixture_path.is_symlink(), "fixture is missing or symbolic")
    raw = fixture_path.read_bytes()
    require(digest(raw) == FIXTURE_SHA256, "fixture digest mismatch")
    try:
        fixture = json.loads(raw)
    except (ValueError, UnicodeError) as error:
        raise VerificationError("invalid fixture JSON") from error
    require(fixture['schema_version'] == 1, "unsupported fixture schema")
    source_dir = root / 'sources'
    require(source_dir.is_dir() and not source_dir.is_symlink(), "source directory missing or symbolic")
    require({p.name for p in source_dir.iterdir()} == SOURCE_NAMES, "closed source inventory mismatch")
    require({s['name'] for s in fixture['sources']} == SOURCE_NAMES, "fixture source inventory mismatch")
    hashes = {}
    for entry in fixture['sources']:
        path = source_dir / entry['name']
        require(path.is_file() and not path.is_symlink(), "source missing, nonregular, or symbolic")
        hashes[entry['name']] = digest(path.read_bytes())
        require(hashes[entry['name']] == entry['sha256'], f"source digest mismatch: {entry['name']}")
    for sequence, entry in fixture['sequences'].items():
        expected = entry['terms']
        observed = parse_bfile((source_dir / entry['source']).read_text(encoding='utf-8'))
        require(expected == [[i, a] for i, a in enumerate(observed)], f"fixture/source disagreement: {sequence}")
    return fixture, hashes


def compositions(total, boxes):
    require(integer(total) and total >= 0, "composition total must be a nonnegative integer")
    require(integer(boxes) and boxes >= 1, "composition boxes must be a positive integer")
    if boxes == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, boxes - 1):
            yield (first,) + rest


def choose(n, k):
    require(integer(n) and n >= 0 and integer(k) and k >= 0, "invalid binomial arguments")
    return math.comb(n, k) if k <= n else 0


def rising(n, k):
    require(integer(n) and n >= 0 and integer(k) and k >= 0, "invalid rising-factorial arguments")
    return math.prod(range(n, n + k))


def pair_list(n):
    return tuple(itertools.combinations(range(n), 2))


def validate_graph(n, multiplicities):
    require(integer(n) and n >= 0, "invalid graph order")
    require(len(multiplicities) == n * (n - 1) // 2, "incorrect graph vector length")
    require(all(integer(x) and x >= 0 for x in multiplicities), "invalid graph multiplicity")


def degrees(n, multiplicities):
    validate_graph(n, multiplicities)
    result = [0] * n
    for (u, v), count in zip(pair_list(n), multiplicities):
        result[u] += count
        result[v] += count
    return result


def connected(n, multiplicities):
    validate_graph(n, multiplicities)
    if n == 0:
        return False  # OEIS C_0=1 is applied separately, never by this predicate.
    adjacency = [set() for _ in range(n)]
    for (u, v), count in zip(pair_list(n), multiplicities):
        if count:
            adjacency[u].add(v)
            adjacency[v].add(u)
    seen = {0}
    todo = [0]
    while todo:
        u = todo.pop()
        for v in adjacency[u] - seen:
            seen.add(v)
            todo.append(v)
    return len(seen) == n


def permutation_maps(n):
    pairs = pair_list(n)
    lookup = {pair: i for i, pair in enumerate(pairs)}
    return [tuple(lookup[tuple(sorted((p[u], p[v])))] for u, v in pairs)
        for p in itertools.permutations(range(n))]


def canonical(n, multiplicities, maps=None):
    validate_graph(n, multiplicities)
    if maps is None:
        maps = permutation_maps(n)
    return min(tuple(multiplicities[j] for j in mapping) for mapping in maps)


def enumerate_graphs(fixture):
    maximum = fixture['enumeration_max_edges']
    require(maximum == 6, "unexpected exhaustive-enumeration scope")
    observed_a = [1, 0]
    observed_c = [1, 0]
    rows = []
    candidates = 0
    leafless_labelled = {}
    connected_labelled = {}
    for m in range(2, maximum + 1):
        total = connected_total = 0
        vertex_rows = []
        # 2m=sum degree >= 2n proves n<=m, so this covers every nonempty graph.
        for n in range(2, m + 1):
            maps = permutation_maps(n)
            all_classes, connected_classes = set(), set()
            labelled = labelled_connected = checked = 0
            for vector in compositions(m, n * (n - 1) // 2):
                checked += 1
                if min(degrees(n, vector)) < 2:
                    continue
                labelled += 1
                key = canonical(n, vector, maps)
                all_classes.add(key)
                if connected(n, vector):
                    labelled_connected += 1
                    connected_classes.add(key)
            require(checked == choose(n * (n - 1) // 2 + m - 1, m), "enumeration missed a composition")
            require(connected_classes <= all_classes, "connected classes missing from total")
            leafless_labelled[n, m] = labelled
            connected_labelled[n, m] = labelled_connected
            candidates += checked
            total += len(all_classes)
            connected_total += len(connected_classes)
            vertex_rows.append({'vertices': n, 'composition_candidates': checked,
                'labelled_leafless': labelled, 'labelled_connected_leafless': labelled_connected,
                'unlabelled_total': len(all_classes), 'unlabelled_connected': len(connected_classes)})
        observed_a.append(total)
        observed_c.append(connected_total)
        rows.append({'edges': m, 'by_vertex_count': vertex_rows})
    for name, observed in [('A307316', observed_a), ('A307317', observed_c)]:
        expected = [v for _, v in fixture['sequences'][name]['terms'][:maximum + 1]]
        require(observed == expected, f"exhaustive canonical count mismatch: {name}")
    monotone_comparisons = 0
    for n in range(2, maximum + 1):
        last_a = last_c = Fraction(0)
        for m in range(maximum + 1):
            denominator = choose(n * (n - 1) // 2 + m - 1, m)
            a = Fraction(leafless_labelled.get((n, m), 0), denominator)
            c = Fraction(connected_labelled.get((n, m), 0), denominator)
            require(last_a <= a and last_c <= c, "finite increasing-event probability decreased")
            last_a, last_c = a, c
            monotone_comparisons += 2
    return {'max_edges': maximum, 'A307316': observed_a, 'A307317': observed_c,
        'composition_candidates': candidates, 'vertex_breakdown': rows,
        'fixed_vertex_monotonicity_comparisons': monotone_comparisons}


def euler_checks(fixture):
    a = [v for _, v in fixture['sequences']['A307316']['terms']]
    c = [v for _, v in fixture['sequences']['A307317']['terms']]
    require(len(a) == len(c) and a[0] == c[0] == 1, "Euler fixture bounds/conventions disagree")
    maximum = len(a) - 1
    # Direct finite expansion of product (1-x^k)^(-C_k), ignoring C_0.
    product = [1] + [0] * maximum
    for k in range(1, maximum + 1):
        updated = [0] * (maximum + 1)
        for i, ai in enumerate(product):
            if not ai:
                continue
            for j in range((maximum - i) // k + 1):
                ways = 1 if j == 0 else (choose(c[k] + j - 1, j) if c[k] else 0)
                updated[i + k * j] += ai * ways
        product = updated
    require(product == a, "Euler direct-product mismatch")
    # Independently, invert the logarithmic derivative n A_n=sum B_k A_(n-k).
    b, recovered = [0] * (maximum + 1), [1] + [0] * maximum
    for n in range(1, maximum + 1):
        b[n] = n * a[n] - sum(b[k] * a[n - k] for k in range(1, n))
        numerator = b[n] - sum(d * recovered[d] for d in range(1, n) if n % d == 0)
        require(numerator % n == 0, "Euler inverse has a nonintegral coefficient")
        recovered[n] = numerator // n
        require(recovered[n] >= 0, "Euler inverse has a negative count")
    require(recovered == c, "Euler inverse mismatch")
    return {'max_edges': maximum, 'terms_checked_in_each_direction': maximum + 1,
        'C_0_used_in_product': False, 'direct_product_and_inverse': 'passed'}


def composition_checks():
    moment_count = 0
    composition_count = 0
    for boxes in range(1, 7):
        for total in range(8):
            vectors = list(compositions(total, boxes))
            require(len(vectors) == choose(boxes + total - 1, total), "weak-composition count mismatch")
            composition_count += len(vectors)
            for internal in range(boxes + 1):
                for order in range(6):
                    lhs = Fraction(sum(choose(sum(a[:internal]), order) for a in vectors), len(vectors))
                    rhs = Fraction(choose(total, order) * rising(internal, order), rising(boxes, order))
                    require(lhs == rhs, "composition factorial-moment mismatch")
                    moment_count += 1
    cut_count = 0
    for n in range(4, 7):
        pairs = pair_list(n)
        boxes = len(pairs)
        for total in range(7):
            vectors = list(compositions(total, boxes))
            for size in range(2, n // 2 + 1):
                cross = [i for i, (u, v) in enumerate(pairs) if u < size <= v]
                observed = sum(all(a[i] == 0 for i in cross) for a in vectors)
                remaining = boxes - size * (n - size)
                require(observed == choose(remaining + total - 1, total), "empty-cut count mismatch")
                product = Fraction(1)
                for i in range(total):
                    product *= Fraction(boxes + i - len(cross), boxes + i)
                require(Fraction(observed, len(vectors)) == product, "empty-cut product mismatch")
                cut_count += 1
    return {'moment_identities': moment_count, 'moment_grid': '1<=M<=6, 0<=m<=7, 0<=K<=M, 0<=r<=5',
        'composition_vectors_for_moments': composition_count, 'empty_cut_identities': cut_count,
        'cut_grid': '4<=n<=6, 0<=m<=6, 2<=s<=floor(n/2)'}


def polya_checks():
    transitions = targets = rows = 0
    for boxes in range(1, 6):
        for total in range(7):
            current = list(compositions(total, boxes))
            next_vectors = set(compositions(total + 1, boxes))
            incoming = defaultdict(Fraction)
            for a in current:
                probability_sum = Fraction(0)
                for i in range(boxes):
                    probability = Fraction(a[i] + 1, boxes + total)
                    b = list(a)
                    b[i] += 1
                    b = tuple(b)
                    require(sum(b) == total + 1 and all(x <= y for x, y in zip(a, b)), "Polya step is not increasing")
                    require(b in next_vectors, "Polya step outside next composition space")
                    probability_sum += probability
                    incoming[b] += probability / len(current)
                    transitions += 1
                require(probability_sum == 1, "Polya transition row not normalized")
                rows += 1
            require(set(incoming) == next_vectors, "Polya coupling misses a target")
            expected = Fraction(1, len(next_vectors))
            require(all(p == expected for p in incoming.values()), "Polya coupling does not preserve uniformity")
            targets += len(next_vectors)
    return {'grid': '1<=N<=5, 0<=k<=6', 'transition_rows': rows,
        'coordinatewise_increasing_transitions': transitions, 'uniform_target_probabilities': targets}


# Exact polynomial arithmetic in one symbolic variable l (or u), coefficients Q.
# A polynomial is its coefficient tuple; a series is a tuple of such polynomials.
def ptrim(p):
    p = list(map(Fraction, p))
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p) if p else (Fraction(0),)


def padd(a, b):
    return ptrim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
        for i in range(max(len(a), len(b)))])


def pscale(a, q):
    return ptrim([x * q for x in a])


def pmul(a, b):
    result = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return ptrim(result)


ZERO, ONE, VARIABLE = ptrim([0]), ptrim([1]), ptrim([0, 1])


def series(values, order):
    return tuple((values[i] if i < len(values) else ZERO) for i in range(order + 1))


def sadd(a, b):
    require(len(a) == len(b), "formal-series order mismatch")
    return tuple(padd(x, y) for x, y in zip(a, b))


def sscale(a, q):
    return tuple(pscale(x, q) for x in a)


def smul(a, b):
    require(len(a) == len(b), "formal-series order mismatch")
    result = [ZERO] * len(a)
    for i in range(len(a)):
        for j in range(len(a) - i):
            result[i + j] = padd(result[i + j], pmul(a[i], b[j]))
    return tuple(result)


def shift(a, k):
    require(integer(k) and k >= 0, "invalid formal-series shift")
    return tuple([ZERO] * min(k, len(a)) + list(a[:max(0, len(a) - k)]))


def sinv(a):
    require(a[0] == ONE, "formal inverse requires constant coefficient 1")
    result = [ONE] + [ZERO] * (len(a) - 1)
    for n in range(1, len(a)):
        acc = ZERO
        for k in range(1, n + 1):
            acc = padd(acc, pmul(a[k], result[n - k]))
        result[n] = pscale(acc, -1)
    return tuple(result)


def slog(a):
    require(a[0] == ONE, "formal logarithm requires constant coefficient 1")
    x = list(a)
    x[0] = ZERO
    result = series([], len(a) - 1)
    power = series([ONE], len(a) - 1)
    for k in range(1, len(a)):
        power = smul(power, tuple(x))
        result = sadd(result, sscale(power, Fraction((-1) ** (k + 1), k)))
    return result


def polynomial_text(p, variable='t'):
    terms = []
    for i in range(len(p) - 1, -1, -1):
        value = p[i]
        if not value:
            continue
        coefficient = str(abs(value.numerator)) if value.denominator == 1 else f'{abs(value.numerator)}/{value.denominator}'
        monomial = '' if i == 0 else variable if i == 1 else f'{variable}^{i}'
        body = coefficient if not monomial else monomial if abs(value) == 1 else f'{coefficient}*{monomial}'
        terms.append(('-' if value < 0 else '+', body))
    if not terms:
        return '0'
    return (('-' if terms[0][0] == '-' else '') + terms[0][1]
        + ''.join(f' {sign} {body}' for sign, body in terms[1:]))


def formal_checks():
    order = 6
    constant = series([ONE], order)
    variable = series([VARIABLE], order)
    # A+log(1-l*z+z*A)=0. The coefficient a_j is linear with coefficient 1.
    a = [ZERO] * (order + 1)
    for j in range(1, order + 1):
        z = sadd(sadd(constant, sscale(shift(variable, 1), -1)), shift(tuple(a), 1))
        a[j] = pscale(slog(z)[j], -1)
    z = sadd(sadd(constant, sscale(shift(variable, 1), -1)), shift(tuple(a), 1))
    require(all(x == ZERO for x in sadd(tuple(a), slog(z))), "forward W recurrence residual nonzero")
    forward = sadd(sscale(tuple(a), 2), sscale(shift(sinv(z), 1), 2))
    expected_forward = [None, ptrim([2, 2]), ptrim([0, 0, 1]), ptrim([0, 0, -1, Fraction(2, 3)])]
    require(list(forward[1:4]) == expected_forward[1:], "displayed forward coefficients disagree")
    # Direct substitution into w-log(w)-1+2/w, independent of using w+log(w)=L.
    regular_w = sadd(sscale(variable, -1), tuple(a))
    log_w = sadd(variable, slog(z))
    direct_forward = sadd(sadd(sadd(regular_w, sscale(log_w, -1)), sscale(constant, -1)), sscale(shift(sinv(z), 1), 2))
    expected_regular = list(forward)
    expected_regular[0] = ptrim([-1, -2])
    require(direct_forward == tuple(expected_regular), "direct forward substitution mismatch")

    # Inverse equation: B+2log Z+log(1-z(u+log Z+1)/Z+2z^2/Z^2)=0.
    b = [ZERO] * (order + 1)
    def inverse_parts(coefficients):
        zz = sadd(sadd(constant, sscale(shift(variable, 1), -2)), shift(tuple(coefficients), 1))
        log_z, inv_z = slog(zz), sinv(zz)
        bracket = sadd(sadd(constant, sscale(shift(smul(sadd(sadd(variable, log_z), constant), inv_z), 1), -1)),
            sscale(shift(smul(inv_z, inv_z), 2), 2))
        return zz, log_z, inv_z, sadd(sscale(log_z, 2), slog(bracket))
    for j in range(1, order + 1):
        b[j] = pscale(inverse_parts(b)[3][j], -1)
    zz, log_z, inv_z, remainder = inverse_parts(b)
    require(all(x == ZERO for x in sadd(tuple(b), remainder)), "inverse recurrence residual nonzero")
    # A second form is the log of Q: B+log(Z^2-z Z(u+log Z)-z Z+2z^2).
    q = sadd(sadd(sadd(smul(zz, zz), sscale(shift(smul(zz, sadd(variable, log_z)), 1), -1)),
        sscale(shift(zz, 1), -1)), sscale(shift(constant, 2), 2))
    require(all(x == ZERO for x in sadd(tuple(b), slog(q))), "inverse Q substitution residual nonzero")
    normalized_denominator = sadd(sadd(sadd(zz, sscale(shift(sadd(variable, log_z), 1), -1)),
        sscale(shift(constant, 1), -1)), sscale(shift(inv_z, 2), 2))
    inverse = sinv(normalized_denominator)
    expected_inverse = [ONE, ptrim([1, 3]), ptrim([-2, -1, 9]),
        ptrim([Fraction(-1, 2), -13, Fraction(-47, 2), 27])]
    require(list(inverse[:4]) == expected_inverse, "displayed inverse coefficients disagree")
    # Basic algebra negative controls independently exercise the series routines.
    require(smul(zz, inv_z) == constant, "formal reciprocal residual nonzero")
    return {'arithmetic': 'exact rational polynomial coefficients, Python standard library',
        'recurrence_residuals_vanish_through_order': order,
        'forward_f_1_through_f_6': [polynomial_text(p, 'l') for p in forward[1:]],
        'inverse_r_0_through_r_6': [polynomial_text(p, 'u') for p in inverse],
        'forward_a_1_through_a_6': [polynomial_text(p, 'l') for p in a[1:]],
        'inverse_b_1_through_b_6': [polynomial_text(p, 'u') for p in b[1:]],
        'scope': 'Finite formal identities; the all-fixed-order theorem requires the analytic remainder argument.'}


def expect_rejected(name, operation, results):
    try:
        operation()
    except VerificationError:
        results.append(name)
    else:
        raise VerificationError(f"adversarial case was accepted: {name}")


def adversarial_checks(root):
    results = []
    expect_rejected('explicit false guard', lambda: require(False, 'intentional'), results)
    expect_rejected('negative composition total', lambda: list(compositions(-1, 2)), results)
    expect_rejected('zero composition boxes', lambda: list(compositions(2, 0)), results)
    expect_rejected('boolean composition input', lambda: list(compositions(True, 2)), results)
    expect_rejected('negative graph multiplicity', lambda: canonical(2, (-1,)), results)
    expect_rejected('wrong graph vector length', lambda: canonical(3, (1,)), results)
    expect_rejected('duplicate b-file index', lambda: parse_bfile('0 1\n0 1\n'), results)
    expect_rejected('missing b-file index', lambda: parse_bfile('0 1\n2 1\n'), results)
    expect_rejected('negative b-file count', lambda: parse_bfile('0 -1\n'), results)
    expect_rejected('nonnumeric b-file count', lambda: parse_bfile('0 x\n'), results)
    expect_rejected('nonunit formal inverse', lambda: sinv(series([ZERO], 2)), results)
    expect_rejected('nonunit formal logarithm', lambda: slog(series([ZERO], 2)), results)
    package_root = root.parent
    expect_rejected('output inside entire package',
        lambda: validate_output_destination(package_root / 'report131.tex', package_root), results)
    expect_rejected('output replaces verifier',
        lambda: validate_output_destination(root / 'verify.py', package_root), results)
    expect_rejected('output replaces source snapshot',
        lambda: validate_output_destination(root / 'sources' / 'b307316.txt', package_root), results)
    expect_rejected('output equals package directory',
        lambda: validate_output_destination(package_root, package_root), results)
    with tempfile.TemporaryDirectory(prefix='report131-output-guards-') as directory:
        external = Path(directory)
        existing = external / 'existing.txt'
        existing.write_text('retain this file', encoding='utf-8')
        expect_rejected('output existing external file',
            lambda: validate_output_destination(existing, package_root), results)
        symbolic_target = external / 'symbolic-target.txt'
        symbolic_target.symlink_to(existing)
        expect_rejected('output symbolic target',
            lambda: validate_output_destination(symbolic_target, package_root), results)
        dangling_target = external / 'dangling-target.txt'
        dangling_target.symlink_to(external / 'absent.txt')
        expect_rejected('output dangling symbolic target',
            lambda: validate_output_destination(dangling_target, package_root), results)
        real_directory = external / 'real-directory'
        real_directory.mkdir()
        symbolic_directory = external / 'symbolic-directory'
        symbolic_directory.symlink_to(real_directory, target_is_directory=True)
        expect_rejected('output symbolic ancestor',
            lambda: validate_output_destination(symbolic_directory / 'out.json', package_root), results)
        expect_rejected('output parent traversal',
            lambda: validate_output_destination(real_directory / '..' / 'out.json', package_root), results)
        expect_rejected('output missing parent directory',
            lambda: validate_output_destination(external / 'absent-directory' / 'out.json', package_root), results)
        exclusive = external / 'exclusive.txt'
        write_exclusive_output(exclusive, package_root, 'first write')
        expect_rejected('exclusive output refuses second write',
            lambda: write_exclusive_output(exclusive, package_root, 'second write'), results)
        require(exclusive.read_text(encoding='utf-8') == 'first write', 'exclusive output replaced existing data')
        raced = external / 'raced.txt'
        validate_output_destination(raced, package_root)
        raced.write_text('concurrently created', encoding='utf-8')
        expect_rejected('exclusive output refuses newly existing target',
            lambda: write_exclusive_output(raced, package_root, 'replacement'), results)
        require(raced.read_text(encoding='utf-8') == 'concurrently created', 'existing output data changed')
        require(existing.read_text(encoding='utf-8') == 'retain this file', 'external fixture data changed')
    # Tamper only isolated temporary copies, never the supplied source snapshots.
    with tempfile.TemporaryDirectory(prefix='report131-adversarial-') as directory:
        temporary = Path(directory)
        shutil.copyfile(root / 'fixtures.json', temporary / 'fixtures.json')
        shutil.copytree(root / 'sources', temporary / 'sources')
        clean_fixture = (temporary / 'fixtures.json').read_bytes()
        (temporary / 'fixtures.json').write_bytes(clean_fixture + b' ')
        expect_rejected('fixture byte corruption', lambda: verify_inputs(temporary), results)
        (temporary / 'fixtures.json').write_bytes(clean_fixture)
        target = temporary / 'sources' / 'b307317.txt'
        clean_source = target.read_bytes()
        target.chmod(0o644)
        target.write_bytes(clean_source + b'\nCORRUPTION\n')
        expect_rejected('public source snapshot corruption', lambda: verify_inputs(temporary), results)
        target.write_bytes(clean_source)
        extra = temporary / 'sources' / 'unlisted.txt'
        extra.write_text('unlisted')
        expect_rejected('extra source inventory member', lambda: verify_inputs(temporary), results)
        extra.unlink()
        target.unlink()
        expect_rejected('missing source inventory member', lambda: verify_inputs(temporary), results)
        target.write_bytes(clean_source)
        bfile = temporary / 'sources' / 'b307316.txt'
        clean_bfile = bfile.read_bytes()
        bfile.chmod(0o644)
        bfile.write_bytes(clean_bfile.replace(b'6 34', b'6 35'))
        expect_rejected('OEIS snapshot count mutation', lambda: verify_inputs(temporary), results)
        bfile.write_bytes(clean_bfile)
        target.unlink()
        target.symlink_to(root / 'sources' / 'b307317.txt')
        expect_rejected('source replaced by symlink', lambda: verify_inputs(temporary), results)
    return {'expected_rejections': len(results), 'rejected_cases': results,
        'guard_mechanism': 'explicit VerificationError, active under python -O'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='new JSON file strictly outside the package; existing or symbolic paths are rejected; stdout is always written')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    destination = validate_output_destination(args.output, root.parent) if args.output else None
    fixture, before = verify_inputs(root)
    result = {'status': 'passed', 'scope': 'Exact finite checks, not certification of the analytic asymptotic theorem.',
        'fixture_sha256': FIXTURE_SHA256, 'source_snapshot_sha256': before,
        'exhaustive_graph_enumeration': enumerate_graphs(fixture),
        'euler_transform': euler_checks(fixture), 'composition_identities': composition_checks(),
        'polya_coupling': polya_checks(), 'formal_series': formal_checks(),
        'adversarial_checks': adversarial_checks(root)}
    _, after = verify_inputs(root)
    require(before == after, 'source snapshots changed during verification')
    result['inputs_unchanged_during_run'] = True
    raw = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if destination is not None:
        write_exclusive_output(destination, root.parent, raw)
    sys.stdout.write(raw)


if __name__ == '__main__':
    try:
        main()
    except (VerificationError, OSError, ValueError, KeyError, TypeError) as error:
        sys.stderr.write(f'VERIFICATION FAILED: {error}\n')
        sys.exit(1)
