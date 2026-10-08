#!/usr/bin/env python3
"""Independently check all binary Fitting basis changes in a certificate.

Default verification checks degree/matching preservation, Qd=dQ, inverse basis
changes, exact reconstruction of every morphism coefficient, and zero mixed
blocks. It certifies the recorded chain isomorphisms. --replay additionally
recomputes the scan from the included PD and compares its certificate and rank.
"""
import argparse
import json
from pathlib import Path
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def xor_rows(left, right):
    return [a ^ b for a, b in zip(left, right)]


def left_scalar(scalar, coefficients):
    out = [[0] * len(coefficients[0]) for _ in scalar]
    for i, row in enumerate(scalar):
        for k, bit in enumerate(row):
            if bit:
                out[i] = xor_rows(out[i], coefficients[k])
    return out


def transpose(matrix):
    return list(map(list, zip(*matrix)))


def right_scalar(coefficients, scalar):
    return transpose(left_scalar(transpose(scalar), transpose(coefficients)))


def dense_inverse(matrix):
    n = len(matrix)
    rows = [list(row) + [int(i == j) for j in range(n)] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next(i for i in range(col, n) if rows[i][col])
        rows[col], rows[pivot] = rows[pivot], rows[col]
        for i in range(n):
            if i != col and rows[i][col]:
                rows[i] = xor_rows(rows[i], rows[col])
    return [row[n:] for row in rows]


def unpack(blocks, columns, n):
    matrix = [[0] * n for _ in range(n)]
    for block, cols in zip(blocks, columns):
        for col, source in enumerate(block):
            for row, target in enumerate(block):
                matrix[target][source] = (cols[col] >> row) & 1
    return matrix


def differential(rows):
    n = len(rows)
    return [[rows[source].get(target, rows[source].get(str(target), 0))
             for source in range(n)] for target in range(n)]


def verify_witness(witness):
    """Dense independent verifier; accepts an in-memory or JSON-roundtripped witness."""
    n = len(witness['rows'])
    q = unpack(witness['blocks'], witness['endomorphism_columns'], n)
    s = unpack(witness['blocks'], witness['basis_columns'], n)
    inverse = dense_inverse(s)
    d = differential(witness['rows'])
    transformed = differential(witness['transformed_rows'])
    for i in range(n):
        for j in range(n):
            if s[i][j] or q[i][j]:
                require(witness['degrees'][i] == witness['degrees'][j], "witness check 1 failed")
                require(witness['matchings'][i] == witness['matchings'][j], "witness check 2 failed")
    require(left_scalar(q, d) == right_scalar(d, q), "witness check 3 failed")
    require(left_scalar(inverse, right_scalar(d, s)) == transformed, "witness check 4 failed")
    require(left_scalar(s, right_scalar(transformed, inverse)) == d, "witness check 5 failed")
    for i in range(n):
        for j in range(n):
            if witness['sides'][i] != witness['sides'][j]:
                require(transformed[i][j] == 0, "witness check 6 failed")
    require(0 < sum(witness['sides']) < n, "witness check 7 failed")
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path, nargs='?',
                        default=Path(__file__).with_name('conway_fitting_witnesses.json'))
    parser.add_argument('--replay', action='store_true')
    args = parser.parse_args()
    certificate = json.loads(args.certificate.read_text())
    for witness in certificate['witnesses']:
        verify_witness(witness)
    if args.replay:
        fast = Path(__file__).resolve().parent.parent / 'fast'
        if not fast.is_dir():
            fast = fast.parent.parent / 'fast'
        sys.path.insert(0, str(fast))
        from fastunknot import Diagram
        from fastunknot.scalar_split import fitting_khovanov_rank
        diagram = Diagram.from_pd(certificate['pd'])
        result = fitting_khovanov_rank(diagram.pd, order=certificate['order'],
                                      record_witnesses=True, check_d_squared=True)
        require(result['rank'] == certificate['rank'], 'replayed rank differs')
        require(json.loads(json.dumps(result['witnesses'])) == certificate['witnesses'],
                'replayed witnesses differ')
    print('Verified', len(certificate['witnesses']), 'scalar Fitting chain isomorphisms'
          + (' and replayed the complete scan.' if args.replay else '.'))

if __name__ == '__main__':
    main()
