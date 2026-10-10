#!/usr/bin/env python3
"""Exact finite audits of the all-weight binary depth-orbit theorem.

The proof is representation-theoretic.  This independent audit constructs
binary Lyndon Lie polynomials, applies the displayed integer letter maps to
word representatives, and computes ranks over Q by integer elimination.
It imports no earlier repository implementation and no numerical periods.
Python standard library only.  Run: python verify_depth_orbits.py --max-weight 10
"""
from argparse import ArgumentParser
from collections import defaultdict
from functools import lru_cache
from fractions import Fraction
from itertools import product
from math import comb, gcd
from pathlib import Path
import json


def mobius(n):
    sign = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        while n % p == 0:
            n //= p
        p += 1
    return -sign if n > 1 else sign


def witt(w, j):
    return sum(mobius(k) * comb(w // k, j // k)
               for k in range(1, gcd(w, j) + 1)
               if w % k == 0 and j % k == 0) // w


def multiplicity(w, j):
    return witt(w, j) - witt(w, j - 1)


def orbit_formula(w, d, directions=None):
    total = 0
    for j in range(1, min(d, w // 2) + 1):
        length = w - 2 * j + 1
        if directions is not None:
            length = min(length, directions * (d - j + 1))
        total += multiplicity(w, j) * length
    return total


def lyndon(word):
    return all(word < word[k:] + word[:k] for k in range(1, len(word)))


def concat(P, Q):
    answer = defaultdict(int)
    for a, ca in P.items():
        for b, cb in Q.items():
            answer[a + b] += ca * cb
    return {w: c for w, c in answer.items() if c}


def bracket(P, Q):
    answer = defaultdict(int, concat(P, Q))
    for w, c in concat(Q, P).items():
        answer[w] -= c
    return {w: c for w, c in answer.items() if c}


def add(P, Q, factor=1):
    result = defaultdict(int, P)
    for word, coefficient in Q.items():
        result[word] += factor * coefficient
    return {word: coefficient for word, coefficient in result.items() if coefficient}


def derivation(P, source, target):
    result = defaultdict(int)
    for word, coefficient in P.items():
        for j, letter in enumerate(word):
            if letter == source:
                changed = word[:j] + (target,) + word[j + 1:]
                result[changed] += coefficient
    return {word: coefficient for word, coefficient in result.items() if coefficient}


@lru_cache(None)
def shuffle_words(u, v):
    if not u:
        return {v: 1}
    if not v:
        return {u: 1}
    answer = defaultdict(int)
    for tail, coefficient in shuffle_words(u[1:], v).items():
        answer[(u[0],) + tail] += coefficient
    for tail, coefficient in shuffle_words(u, v[1:]).items():
        answer[(v[0],) + tail] += coefficient
    return dict(answer)


def shuffle_vectors(P, Q):
    answer = defaultdict(int)
    for u, a in P.items():
        for v, b in Q.items():
            for word, coefficient in shuffle_words(u, v).items():
                answer[word] += a * b * coefficient
    return {word: coefficient for word, coefficient in answer.items() if coefficient}


@lru_cache(None)
def lie(word):
    if len(word) == 1:
        return {word: 1}
    split = next(k for k in range(1, len(word)) if lyndon(word[k:]))
    return bracket(lie(word[:split]), lie(word[split:]))


def matrix_product(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))


def transform_word(word, A):
    result = {(): 1}
    for letter in word:
        result = concat(result, {(k,): A[k][letter]
                                 for k in range(2) if A[k][letter]})
    return result


def normalize(row):
    row = {j: c for j, c in row.items() if c}
    if not row:
        return row
    divisor = 0
    for c in row.values():
        divisor = gcd(divisor, c)
    if row[min(row)] < 0:
        divisor = -divisor
    return {j: c // divisor for j, c in row.items()}


class ExactRowSpace:
    """Rational rank, preserving integral rows and removing gcds."""
    def __init__(self):
        self.pivots = {}

    def insert(self, values):
        row = normalize({j: c for j, c in enumerate(values) if c})
        while row:
            j = min(row)
            if j not in self.pivots:
                self.pivots[j] = row
                return True
            old = self.pivots[j]
            a, b = row[j], old[j]
            divisor = gcd(a, b)
            a //= divisor
            b //= divisor
            reduced = {k: b * c for k, c in row.items()}
            for k, c in old.items():
                reduced[k] = reduced.get(k, 0) - a * c
            row = normalize(reduced)
        return False

    def __len__(self):
        return len(self.pivots)


def pair_word_vector(P, L):
    return sum(c * P.get(word, 0) for word, c in L.items())


def span_rows(words, primitives, maps):
    space = ExactRowSpace()
    for word in words:
        for A in maps:
            transformed = transform_word(word, A)
            space.insert([pair_word_vector(transformed, L) for L in primitives])
    return space


def rank_rows(words, primitives, maps):
    return len(span_rows(words, primitives, maps))


def verify_explicit_certificates(output_dir):
    I = ((1, 0), (0, 1))
    R = ((0, -1), (-1, 0))
    M = ((1, 0), (1, -1))
    six = [I, R, M, matrix_product(R, M), matrix_product(M, R),
           matrix_product(matrix_product(R, M), R)]
    # New weight-seven congruence, before endpoint transport.
    target = (0, 0, 0, 0, 1, 1, 1)
    singles = (0, 0, 0, 0, 0, 0, 1)
    doubles = (0, 0, 0, 0, 0, 1, 1)
    residual = {target: 1}
    descriptors = [(I, singles, -3), (I, doubles, 2),
                   (R, singles, 2), (R, doubles, -1),
                   (M, singles, -3), (M, doubles, 1)]
    for matrix, word, coefficient in descriptors:
        residual = add(residual, transform_word(word, matrix), -coefficient)
    assert all(pair_word_vector(residual, lie(word)) == 0
               for word in product((0, 1), repeat=7) if lyndon(word))

    # Eulerian-idempotent formula produces every product correction.
    # R = sum_{k>=2} (-1)^k/k sum_{R=w1...wk} w1 shuffle ... shuffle wk.
    products = defaultdict(Fraction)
    for word, coefficient in residual.items():
        for cuts in range(1, 1 << (len(word) - 1)):
            boundaries = [0] + [j for j in range(1, len(word))
                                if cuts & (1 << (j - 1))] + [len(word)]
            pieces = [word[a:b] for a, b in zip(boundaries, boundaries[1:])]
            k = len(pieces)
            products[tuple(sorted(pieces))] += Fraction(coefficient * (-1)**k, k)
    products = {factors: coefficient for factors, coefficient in products.items()
                if coefficient}
    reexpanded = {}
    for factors, coefficient in products.items():
        expanded = {(): coefficient}
        for factor in factors:
            expanded = shuffle_vectors(expanded, {factor: 1})
        reexpanded = add(reexpanded, expanded)
    assert reexpanded == residual
    product_certificate = {
        'status': 'PASS', 'weight': 7,
        'word_convention': 'outer-letter-first; 0=dt/t, 1=dt/(1-t)',
        'residual': [{'word': ''.join(map(str, word)), 'coefficient': coefficient}
                     for word, coefficient in sorted(residual.items())],
        'product_correction': [
            {'coefficient': str(coefficient),
             'factors': [''.join(map(str, factor)) for factor in factors]}
            for factors, coefficient in sorted(products.items())],
        'exact_shuffle_reexpansion_residual': 0,
        'number_of_product_monomials': len(products)}
    (output_dir / 'weight7_height_one_products.json').write_text(
        json.dumps(product_certificate, indent=2) + '\n')

    # New weight-eight obstruction.  Normalize so its target coefficient is 1.
    x, y = {(0,): 1}, {(1,): 1}
    highest = y
    for _ in range(7):
        highest = bracket(x, highest)
    powers = [highest]
    for _ in range(4):
        powers.append(derivation(powers[-1], 0, 1))
    omega = add(add(powers[4], powers[3], -6), powers[2], 12)
    assert omega[(0, 0, 0, 0, 0, 1, 1, 1)] == 360
    # Audit every low-depth binary word, including all trailing-zero cases.
    tested = 0
    for word in product((0, 1), repeat=8):
        if sum(word) <= 2:
            for matrix in six:
                assert pair_word_vector(transform_word(word, matrix), omega) == 0
                tested += 1
    # Audit every possible nonempty shuffle product at weight eight.
    shuffle_count = 0
    for p in range(1, 8):
        for u in product((0, 1), repeat=p):
            for v in product((0, 1), repeat=8 - p):
                assert pair_word_vector(shuffle_words(u, v), omega) == 0
                shuffle_count += 1
    obstruction_certificate = {
        'status': 'PASS', 'weight': 8, 'normalizing_denominator': 360,
        'target_word': '00000111', 'target_pairing': '1',
        'integer_lie_polynomial': {''.join(map(str, word)): coefficient
                                   for word, coefficient in sorted(omega.items())},
        'all_low_depth_transformed_words_checked': tested,
        'all_nonempty_shuffle_products_checked': shuffle_count,
        'claim': 'formal six-argument depth-two nonmembership, not numerical periods'}
    (output_dir / 'weight8_height_one_obstruction.json').write_text(
        json.dumps(obstruction_certificate, indent=2) + '\n')
    return {'weight7_product_monomials': len(products),
            'weight7_exact_reexpansion': 'PASS',
            'weight8_obstruction': 'PASS',
            'weight8_transformed_word_checks': tested,
            'weight8_shuffle_product_checks': shuffle_count}


def verify(max_weight):
    I = ((1, 0), (0, 1))
    R = ((0, -1), (-1, 0))
    M = ((1, 0), (1, -1))
    six = [I, R, M, matrix_product(R, M), matrix_product(M, R),
           matrix_product(matrix_product(R, M), R)]
    assert len(set(six)) == 6
    assert {matrix_product(A, B) for A in six for B in six} == set(six)
    rows = []
    direction_checks = []
    height_one_checks = []
    for w in range(2, max_weight + 1):
        words = [word for word in product((0, 1), repeat=w) if lyndon(word)]
        primitives = [lie(word) for word in words]
        assert len(words) == sum(witt(w, j) for j in range(w + 1))
        assert len(words) == sum(multiplicity(w, j) * (w - 2*j + 1)
                                 for j in range(1, w // 2 + 1))
        assert all(multiplicity(w, j) >= 0 for j in range(1, w // 2 + 1))
        for d in range(1, w // 2 + 1):
            seeds = [word for word in words if sum(word) <= d]
            six_span = span_rows(seeds, primitives, six)
            observed = len(six_span)
            expected = orbit_formula(w, d, 3)
            assert observed == expected, (w, d, observed, expected)
            # Enough distinct directions realize the complete GL2 orbit.
            # x -> x+k*y, y -> y; k ranges over w distinct integers.
            linear_maps = [((1, 0), (k, 1)) for k in range(w)]
            observed_full = rank_rows(seeds, primitives, linear_maps)
            expected_full = orbit_formula(w, d)
            assert observed_full == expected_full, (w, d, observed_full, expected_full)
            for h in range(1, w):
                target = (0,) * (w - h) + (1,) * h
                trial = ExactRowSpace()
                trial.pivots = dict(six_span.pivots)
                member = not trial.insert([L.get(target, 0) for L in primitives])
                threshold = min(h, w - h, (w + 1) // 3)
                assert member == (d >= threshold), (w, h, d, member, threshold)
                height_one_checks.append(dict(weight=w, height=h, depth=d,
                                              member=member, minimum_depth=threshold))
            rows.append(dict(weight=w, depth=d, quotient_dimension=len(words),
                             initial_depth_dimension=len(seeds),
                             six_actual=observed, six_formula=expected,
                             linear_actual=observed_full, linear_formula=expected_full))
        # For depth two, audit dependence only on the number of directions.
        if w >= 4:
            seeds = [word for word in words if sum(word) <= 2]
            for k in range(1, min(w, 5) + 1):
                # Irregularly spaced rational directions, not the six-map group.
                chosen = [((1, 0), (t*t+t, 1)) for t in range(k)]
                observed = rank_rows(seeds, primitives, chosen)
                expected = orbit_formula(w, 2, k)
                assert observed == expected, (w, k, observed, expected)
                direction_checks.append(dict(weight=w, directions=k,
                                             actual=observed, formula=expected))
        print(json.dumps({'weight': w, 'status': 'PASS',
                          'quotient_dimension': len(words)}), flush=True)
    return {'status': 'PASS',
            'scope': 'formal binary shuffle indecomposables and letter substitutions',
            'numerical_period_independence': False,
            'max_weight': max_weight, 'word_rank_checks': rows,
            'finite_direction_checks': direction_checks,
            'height_one_membership_checks': height_one_checks}


if __name__ == '__main__':
    parser = ArgumentParser()
    parser.add_argument('--max-weight', type=int, default=10)
    parser.add_argument('--output', default='depth_orbit_verification.json')
    args = parser.parse_args()
    result = verify(args.max_weight)
    result['explicit_certificates'] = verify_explicit_certificates(Path(args.output).parent)
    Path(args.output).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'output': args.output,
                      'word_rank_cases': len(result['word_rank_checks']),
                      'direction_cases': len(result['finite_direction_checks'])}))
