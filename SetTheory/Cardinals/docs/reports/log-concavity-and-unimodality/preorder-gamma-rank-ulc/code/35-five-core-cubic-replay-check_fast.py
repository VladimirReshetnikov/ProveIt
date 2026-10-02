#!/usr/bin/env python3
"""Optimized independent exact five-core/two-sink cubic checker (Python standard library).

Usage: python check.py SOURCE [--partial] [--workers N] [--output RECEIPT]
Without --partial, exactly all 9608 certificates are required. Partial mode
checks a fixed snapshot of the filenames available at the start and never
claims that the certificate collection is complete. Every run checks all
2^20 labeled core relations through disjoint permutation-orbit coverage.
No producer module is imported or executed.
"""
from pathlib import Path
from itertools import combinations, permutations
from collections import defaultdict, Counter
from fractions import Fraction
from math import lcm
from concurrent.futures import ProcessPoolExecutor
import argparse
import hashlib
import json
import re
import time

CORE = tuple(range(5))
VERTICES = tuple(range(7))
SINKS = (5, 6)
DIM = 12
RADIX = 16
UNIT = tuple(RADIX ** i for i in range(DIM))
ARCS = tuple((i, j) for i in CORE for j in CORE if i != j)
ARC_INDEX = {arc: n for n, arc in enumerate(ARCS)}
EXPECTED_CLASSES = 9608
TARGET = 'gamma2^2-3gamma1gamma3'
VARIABLES = [f'u{i}' for i in CORE] + [f'v{i}' for i in CORE] + ['w0', 'w1']


def require(condition, message):
    if not condition:
        raise ValueError(message)


def head_unit(j):
    return UNIT[5 + j] if j < 5 else UNIT[10 + j - 5]


def pack(exponent):
    require(isinstance(exponent, list) and len(exponent) == DIM,
            f'Expected a length-{DIM} exponent list: {exponent!r}')
    require(all(type(x) is int and 0 <= x <= 8 for x in exponent),
            f'Invalid nonnegative integer exponent: {exponent!r}')
    require(sum(exponent) <= 8, f'Exponent exceeds total degree eight: {exponent!r}')
    return sum(e * u for e, u in zip(exponent, UNIT))


def rational(x):
    require(type(x) in (int, str), f'Rational must be exact integer or string: {x!r}')
    return Fraction(x)


# Literal disjoint physical endpoint pairs. For each pair, list all full
# matching witnesses, not just internal-head injections. Universal sink arcs
# require no core arc bits. Duplicate witness masks are merged; feasibility
# remains a single Boolean and a feasible support contributes coefficient 1.
LITERAL = []
for k in range(4):
    for tails in combinations(CORE, k):
        available_heads = tuple(j for j in VERTICES if j not in tails)
        for heads in combinations(available_heads, k):
            witnesses = set()
            for targets in permutations(heads):
                mask = 0
                for i, j in zip(tails, targets):
                    if j < 5:
                        mask |= 1 << ARC_INDEX[i, j]
                witnesses.add(mask)
            exponent = sum(UNIT[i] for i in tails) + sum(head_unit(j) for j in heads)
            LITERAL.append((k, exponent, tuple(witnesses)))


# Separate grouped construction: choose core heads, check Hall on their
# incoming neighborhoods within the selected tail set, and explicitly expand
# the elementary symmetric polynomial in the two selected sink variables.
GROUPED = []
for k in range(4):
    for tails in combinations(CORE, k):
        tailmask = sum(1 << i for i in tails)
        for r in range(min(k, 5 - k) + 1):
            if k - r > 2:
                continue
            for heads in combinations(tuple(j for j in CORE if j not in tails), r):
                exponent = sum(UNIT[i] for i in tails) + sum(UNIT[5+j] for j in heads)
                sink_exponents = tuple(sum(head_unit(j) for j in chosen)
                                       for chosen in combinations(SINKS, k-r))
                GROUPED.append((k, tailmask, heads, exponent, sink_exponents))


def hall_covers(tailmask, heads, incoming):
    neighborhoods = tuple(incoming[j] & tailmask for j in heads)
    for subset in range(1, 1 << len(heads)):
        union = 0
        for r, neighbors in enumerate(neighborhoods):
            if subset >> r & 1:
                union |= neighbors
        if union.bit_count() < subset.bit_count():
            return False
    return True


def construct_gammas(code, rows):
    literal = [dict() for _ in range(4)]
    for k, exponent, witnesses in LITERAL:
        if any(code & mask == mask for mask in witnesses):
            require(exponent not in literal[k], 'Duplicate literal support monomial')
            literal[k][exponent] = 1
    incoming = tuple(sum(1 << i for i in CORE if rows[i] >> j & 1) for j in CORE)
    grouped = [dict() for _ in range(4)]
    for k, tailmask, heads, exponent, sink_exponents in GROUPED:
        if hall_covers(tailmask, heads, incoming):
            for sink_exponent in sink_exponents:
                monomial = exponent + sink_exponent
                require(monomial not in grouped[k], 'Duplicate grouped support monomial')
                grouped[k][monomial] = 1
    require(literal == grouped, f'Literal/Hall support mismatch for rows {rows}')
    require(literal[0] == {0: 1}, 'Incorrect empty support')
    return literal


def add_product(target, left, right, scalar):
    for e, c in left.items():
        for f, d in right.items():
            target[e+f] += scalar*c*d


def check_one(job):
    source, ident, code, rows = job
    path = Path(source) / 'two-sink-cubic' / f'certificate_{ident}.json'
    raw = path.read_bytes()
    cert = json.loads(raw)
    require(set(cert) == {'rows', 'sink_count', 'target', 'terms'},
            f'Unsupported certificate fields, id {ident}: {list(cert)}')
    require(cert['rows'] == list(rows), f'Row mismatch, id {ident}')
    require(type(cert['sink_count']) is int and cert['sink_count'] == 2,
            f'Wrong sink count, id {ident}')
    require(cert['target'] == TARGET, f'Wrong target, id {ident}')
    require(isinstance(cert['terms'], list), f'Wrong term array, id {ident}')
    gamma = construct_gammas(code, rows)
    target = defaultdict(int)
    add_product(target, gamma[2], gamma[2], 1)
    add_product(target, gamma[1], gamma[3], -3)
    target = {e: c for e, c in target.items() if c}
    remainder = dict(target)
    lengths = Counter()
    for index, square in enumerate(cert['terms']):
        require(isinstance(square, list) and len(square) == 2,
                f'Malformed square {index}, id {ident}')
        weight = rational(square[0])
        require(weight > 0, f'Nonpositive square weight {index}, id {ident}')
        meta = square[1]
        require(isinstance(meta, list) and len(meta) == 2,
                f'Malformed square metadata {index}, id {ident}')
        multiplier, inside = meta
        outer = pack(multiplier)
        outer_degree = sum(multiplier)
        require(isinstance(inside, list) and len(inside) > 0,
                f'Empty/malformed square polynomial {index}, id {ident}')
        terms = []
        for term in inside:
            require(isinstance(term, list) and len(term) == 2,
                    f'Malformed inner term {index}, id {ident}')
            exponent, coefficient = term
            packed = pack(exponent)
            require(outer_degree + 2*sum(exponent) == 8,
                    f'Nonhomogeneous degree-eight square {index}, id {ident}')
            terms.append((packed, rational(coefficient)))
        lengths[len(terms)] += 1
        # Clear inner denominators exactly once. The identity is
        # weight * (sum c_i*x^e_i)^2
        #   = (weight / L^2) * (sum (L*c_i)*x^e_i)^2.
        # Diagonal and doubled unordered cross terms give the full expansion.
        # Coalesce its integer coefficients before applying the rational scale.
        # No target-support restriction is applied: absent exponents are checked.
        denominator = lcm(*(c.denominator for _, c in terms))
        integer_terms = [(e, c.numerator*(denominator//c.denominator)) for e,c in terms]
        expansion = defaultdict(int)
        for i, (e,c) in enumerate(integer_terms):
            expansion[outer+2*e] += c*c
            for f,d in integer_terms[i+1:]:
                expansion[outer+e+f] += 2*c*d
        scale = weight / (denominator*denominator)
        for key,coefficient in expansion.items():
            if coefficient:
                remainder[key] = remainder.get(key,0) - scale*coefficient
    negatives = [(e,c) for e,c in remainder.items() if c < 0]
    if negatives:
        e, c = min(negatives, key=lambda pair: pair[1])
        exponent = [(e//u) % RADIX for u in UNIT]
        raise ValueError(f'Negative exact remainder, id {ident}, exponent {exponent}, coefficient {c}')
    return {
        'id': ident,
        'certificate_sha256': hashlib.sha256(raw).hexdigest(),
        'square_count': len(cert['terms']),
        'square_length_histogram': dict(sorted(lengths.items())),
        'gamma_support_counts': [len(g) for g in gamma],
        'target_term_count': len(target),
        'negative_target_term_count': sum(c < 0 for c in target.values()),
        'coefficientwise_nonnegative_target': all(c >= 0 for c in target.values()),
        'positive_remainder_term_count': sum(c > 0 for c in remainder.values()),
        'literal_and_grouped_hall_support_equal': True,
    }


def read_catalog(path):
    raw = path.read_bytes()
    cores = []
    for lineno, line in enumerate(raw.decode().splitlines(), 1):
        values = list(map(int, line.split()))
        require(len(values) == 6, f'Malformed catalog line {lineno}')
        code, *rows = values
        require(0 <= code < (1 << 20), f'Invalid catalog code on line {lineno}')
        require(all(0 <= row < 32 and not (row >> i & 1) for i, row in enumerate(rows)),
                f'Non-loopless/invalid rows on line {lineno}')
        actual = sum(1 << a for a,(i,j) in enumerate(ARCS) if rows[i] >> j & 1)
        require(actual == code, f'Rows/code mismatch on line {lineno}')
        cores.append((code, tuple(rows)))
    require(len(cores) == EXPECTED_CLASSES, f'Wrong catalog length: {len(cores)}')
    return cores, hashlib.sha256(raw).hexdigest()


def check_coverage(cores):
    maps = tuple(tuple(1 << ARC_INDEX[p[i],p[j]] for i,j in ARCS)
                 for p in permutations(CORE))
    seen = bytearray(1 << 20)
    orbit_sizes = Counter()
    for ident, (code, rows) in enumerate(cores):
        edges = tuple(i for i in range(20) if code >> i & 1)
        orbit = {sum(mapping[i] for i in edges) for mapping in maps}
        require(min(orbit) == code, f'Nonminimal orbit representative, id {ident}')
        require(all(not seen[x] for x in orbit), f'Intersecting catalog orbits, id {ident}')
        for x in orbit:
            seen[x] = 1
        orbit_sizes[len(orbit)] += 1
    require(all(seen), f'Incomplete orbit coverage: {len(seen)-sum(seen)} missing')
    return {'labeled_core_count': len(seen), 'representative_count': len(cores),
            'permutations_per_representative': len(maps),
            'orbits_disjoint': True, 'all_labeled_cores_covered': True,
            'orbit_size_histogram': dict(sorted(orbit_sizes.items()))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--partial', action='store_true')
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('receipt.json'))
    args = parser.parse_args()
    require(args.workers >= 1, 'Worker count must be positive')
    started = time.time()
    cores, catalog_hash = read_catalog(args.source/'cores.txt')
    files = list((args.source/'two-sink-cubic').glob('certificate_*.json'))
    ids = []
    for path in files:
        match = re.fullmatch(r'certificate_(0|[1-9][0-9]*)\.json', path.name)
        require(match is not None, f'Malformed certificate filename: {path.name}')
        ident = int(match.group(1))
        require(0 <= ident < len(cores), f'Out-of-range certificate: {path.name}')
        ids.append(ident)
    ids.sort()
    require(ids, 'No certificates found')
    if not args.partial:
        require(ids == list(range(EXPECTED_CLASSES)),
                f'Incomplete certificate collection: {len(ids)} of {EXPECTED_CLASSES}')
    print(f'Checking {len(ids)} certificates; partial mode={args.partial}', flush=True)
    records = []
    jobs = ((str(args.source), ident, cores[ident][0], cores[ident][1]) for ident in ids)
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        for record in pool.map(check_one, jobs, chunksize=4):
            records.append(record)
            if len(records) % 100 == 0:
                print(f'Checked {len(records)} in {time.time()-started:.2f}s', flush=True)
    print('Checking all 2^20 labeled core relations through disjoint orbits', flush=True)
    coverage = check_coverage(cores)
    require(hashlib.sha256((args.source/'cores.txt').read_bytes()).hexdigest() == catalog_hash,
            'Catalog changed during verification')
    for record in records:
        path = args.source/'two-sink-cubic'/f"certificate_{record['id']}.json"
        require(hashlib.sha256(path.read_bytes()).hexdigest() == record['certificate_sha256'],
                f'Certificate changed during verification: {path.name}')
    lengths = Counter()
    for record in records:
        lengths.update(record['square_length_histogram'])
    manifest_hash = hashlib.sha256('\n'.join(
        f"{r['id']}:{r['certificate_sha256']}" for r in records).encode()).hexdigest()
    receipt = {
        'status': 'PARTIAL_PASS' if args.partial else 'PASS',
        'complete_certificate_collection_verified': not args.partial,
        'certificate_count': len(records), 'expected_certificate_count': EXPECTED_CLASSES,
        'verified_certificate_ids': ids if args.partial else 'all IDs 0 through 9607',
        'target': TARGET, 'variables': VARIABLES, 'homogeneous_degree': 8,
        'arithmetic': 'Exact integers and fractions.Fraction only',
        'standard_library_only': True, 'producer_code_imported_or_executed': False,
        'support_method': 'Literal disjoint physical endpoint pairs and full Boolean matching witnesses, independently cross-checked against grouped core-head Hall feasibility and explicit two-sink elementary symmetric polynomials',
        'literal_endpoint_pair_candidates_per_core': len(LITERAL),
        'grouped_core_head_candidates_per_core': len(GROUPED),
        'all_literal_and_hall_polynomials_equal': True,
        'all_exact_remainders_coefficientwise_nonnegative': True,
        'full_square_expansion_including_absent_target_exponents': True,
        'positive_rational_square_count': sum(r['square_count'] for r in records),
        'empty_certificate_count': sum(r['square_count'] == 0 for r in records),
        'square_length_histogram': dict(sorted(lengths.items())),
        'coefficientwise_nonnegative_target_count': sum(r['coefficientwise_nonnegative_target'] for r in records),
        'positive_remainder_term_count': sum(r['positive_remainder_term_count'] for r in records),
        'zero_remainder_count': sum(r['positive_remainder_term_count'] == 0 for r in records),
        'coverage': coverage,
        'checked_source_files_unchanged_during_run': True,
        'catalog_sha256': catalog_hash, 'certificate_manifest_sha256': manifest_hash,
        'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'seconds': round(time.time()-started, 3),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2)+'\n')
    args.output.with_name(args.output.stem+'-manifest.json').write_text(json.dumps(records, indent=2)+'\n')
    print(json.dumps(receipt, indent=2), flush=True)


if __name__ == '__main__':
    main()
