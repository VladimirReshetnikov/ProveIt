#!/usr/bin/env python3
"""Exact weight-six depth obstruction; Python standard library only.

This verifies a formal shuffle/letter-transformation statement. It does not
assert numerical independence of any special polylogarithmic values.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
from pathlib import Path


def add(P, Q, factor=1):
    ans = dict(P)
    for word, coefficient in Q.items():
        ans[word] = ans.get(word, 0) + factor * coefficient
        if not ans[word]:
            del ans[word]
    return ans


def concatenate(P, Q):
    ans = Counter()
    for u, a in P.items():
        for v, b in Q.items():
            ans[u + v] += a * b
    return {w: c for w, c in ans.items() if c}


def bracket(P, Q):
    return add(concatenate(P, Q), concatenate(Q, P), -1)


@lru_cache(maxsize=None)
def shuffle(u, v):
    if not u:
        return {v: 1}
    if not v:
        return {u: 1}
    ans = Counter()
    for w, c in shuffle(u[1:], v).items():
        ans[(u[0],) + w] += c
    for w, c in shuffle(u, v[1:]).items():
        ans[(v[0],) + w] += c
    return dict(ans)


def substitute(P, matrix):
    ans = {}
    for word, coefficient in P.items():
        term = {(): coefficient}
        for letter in word:
            image = {(j,): matrix[j][letter] for j in (0, 1)
                     if matrix[j][letter]}
            term = concatenate(term, image)
        ans = add(ans, term)
    return ans


def pairing(P, Q):
    return sum(a * Q.get(w, 0) for w, a in P.items())


def multiply(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in (0, 1))
                       for j in (0, 1)) for i in (0, 1))


def determinant(A):
    rows = [[Fraction(c) for c in row] for row in A]
    answer = Fraction(1)
    for j in range(len(rows)):
        pivot = next((k for k in range(j, len(rows)) if rows[k][j]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != j:
            rows[pivot], rows[j] = rows[j], rows[pivot]
            answer = -answer
        a = rows[j][j]
        answer *= a
        for k in range(j + 1, len(rows)):
            factor = rows[k][j] / a
            for h in range(j + 1, len(rows)):
                rows[k][h] -= factor * rows[j][h]
            rows[k][j] = 0
    return answer


def lyndon(word):
    return bool(word) and all(word < word[k:] + word[:k]
                              for k in range(1, len(word)))


@lru_cache(maxsize=None)
def lyndon_bracket(word):
    if len(word) == 1:
        return {word: 1}
    # Standard factorization: longest proper Lyndon suffix.
    for k in range(1, len(word)):
        if lyndon(word[k:]):
            return bracket(lyndon_bracket(word[:k]),
                           lyndon_bracket(word[k:]))
    raise ValueError('Input is not a Lyndon word')


def word(text):
    return tuple(map(int, text))


def verify():
    x, y = {(0,): 1}, {(1,): 1}
    commutator = bracket(x, y)
    omega = bracket(bracket(x, commutator), bracket(y, commutator))
    I = ((1, 0), (0, 1))
    R = ((0, -1), (-1, 0))
    M = ((1, 0), (1, -1))
    group = [I, R, M, multiply(R, M), multiply(M, R),
             multiply(multiply(R, M), R)]
    words = list(product((0, 1), repeat=6))
    lyndon_words = [w for w in words if lyndon(w)]
    assert len(lyndon_words) == 9
    primitive_basis = [lyndon_bracket(w) for w in lyndon_words]
    # Lie primitives annihilate shuffle products; verify every split too.
    shuffle_tests = 0
    for p in range(1, 6):
        for u in product((0, 1), repeat=p):
            for v in product((0, 1), repeat=6-p):
                assert pairing(omega, shuffle(u, v)) == 0
                shuffle_tests += 1
    for matrix in group:
        det = determinant(matrix)
        assert substitute(omega, matrix) == {w: det**3 * c
                                             for w, c in omega.items()}
        for w in words:
            if sum(w) <= 2:
                assert pairing(omega, substitute({w: 1}, matrix)) == 0
    initial_words = [word(s) for s in ('000001', '000011', '000101')]
    rows = [(name, w, substitute({w: 1}, matrix))
            for name, matrix in [('I', I), ('R', R), ('M', M)]
            for w in initial_words]
    matrix = [[pairing(P, L) for L in primitive_basis]
              for _, _, P in rows]
    independent_rows = [0, 1, 2, 3, 4, 5, 6, 8]
    minor_columns = [0, 1, 2, 3, 4, 6, 7, 8]
    minor = [[matrix[i][j] for j in minor_columns] for i in independent_rows]
    assert determinant(minor) == 1
    triple_words = [word(s) for s in ('000111', '001011', '001101')]
    assert [omega.get(w, 0) for w in triple_words] == [0, -1, 2]
    # Two exact congruences modulo shuffle products.
    congruences = [
        ({word('000111'): 1}, [-1, 1, 0, 1, -1, 0, -1, 0, 0]),
        ({word('001011'): 2, word('001101'): 1},
         [-1, 1, 1, -10, 10, 1, -1, 0, -1]),
    ]
    for target, coefficients in congruences:
        residual = dict(target)
        for coefficient, (_, _, P) in zip(coefficients, rows):
            residual = add(residual, P, -coefficient)
        assert all(pairing(residual, L) == 0 for L in primitive_basis)
    return {
        'result': 'PASS',
        'claim': 'Formal weight-six shuffle/letter-transformation quotient',
        'numerical_period_independence': False,
        'quotient_dimension': 9,
        'depth_two_orbit_dimension': 8,
        'remaining_dimension': 1,
        'shuffle_products_checked': shuffle_tests,
        'lyndon_words': [''.join(map(str, w)) for w in lyndon_words],
        'rows': [name + ':' + ''.join(map(str, w)) for name, w, _ in rows],
        'pairing_matrix': matrix,
        'minor_rows': independent_rows,
        'minor_columns': minor_columns,
        'minor_determinant': 1,
        'omega': {''.join(map(str, w)): c for w, c in sorted(omega.items())},
        'triple_values': [0, -1, 2],
        'congruence_coefficients': [coefficients for _, coefficients in congruences],
    }


if __name__ == '__main__':
    receipt = verify()
    output = Path(__file__).resolve().parents[1] / 'data/depth_s3_certificate.json'
    output.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({key: receipt[key] for key in
                     ('result', 'quotient_dimension', 'depth_two_orbit_dimension',
                      'remaining_dimension', 'minor_determinant',
                      'shuffle_products_checked')}))
