#!/usr/bin/env python3
"""A fair reference enumeration of finite Q_PSC refutation certificates.

With ideal unbounded finite storage, search() returns iff Q_PSC is inconsistent.
This Python program is not a binary Turing table or a proof-assistant theorem.
Host resource failures and --limit completion are not mathematical machine halts.
The certificate decoder never admits the checker's optional theorem mode.
"""
from __future__ import annotations

import argparse
import itertools
import json
from math import isqrt
from typing import Any

from environment_tableau import check_certificate


def pair(a: int, b: int) -> int:
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def decode_matrix(n: int) -> list:
    if n == 0:
        return ['B']
    q, tag = divmod(n - 1, 3)
    a, b = unpair(q)
    if tag == 0:
        return ['E', a, b]
    if tag == 1:
        return ['I', decode_matrix(a), decode_matrix(b)]
    return ['A', a, decode_matrix(b)]


def encode_matrix(matrix: list | tuple) -> int:
    tag = matrix[0]
    if tag == 'B':
        return 0
    if tag == 'E':
        return 1 + 3 * pair(matrix[1], matrix[2])
    if tag == 'I':
        return 2 + 3 * pair(encode_matrix(matrix[1]), encode_matrix(matrix[2]))
    if tag == 'A':
        return 3 + 3 * pair(matrix[1], encode_matrix(matrix[2]))
    raise ValueError('Only bottom, membership, implication and universal are enumerated')


def decode_list(n: int) -> list[int]:
    result = []
    while n:
        head, n = unpair(n - 1)
        result.append(head)
    return result


def encode_list(values: list[int]) -> int:
    result = 0
    for value in reversed(values):
        result = 1 + pair(value, result)
    return result


def decode_proof(n: int) -> list:
    q, tag = divmod(n, 6)
    if tag == 1:
        return ['bottom', q]
    a, b = unpair(q)
    if tag == 0:
        return ['close', a, b]
    if tag == 2:
        return ['imp', a, decode_proof(b)]
    if tag == 4:
        return ['all', a, decode_proof(b)]
    c, d = unpair(b)
    if tag == 3:
        return ['imp', a, decode_proof(c), decode_proof(d)]
    return ['all', a, c, decode_proof(d)]


def encode_proof(proof: list) -> int:
    tag = proof[0]
    if tag == 'close' and len(proof) == 3:
        return 6 * pair(proof[1], proof[2])
    if tag == 'bottom' and len(proof) == 2:
        return 6 * proof[1] + 1
    if tag in ('imp', 'all') and len(proof) == 3:
        return 6 * pair(proof[1], encode_proof(proof[2])) + (2 if tag == 'imp' else 4)
    if tag == 'imp' and len(proof) == 4:
        return 6 * pair(proof[1], pair(encode_proof(proof[2]), encode_proof(proof[3]))) + 3
    if tag == 'all' and len(proof) == 4:
        return 6 * pair(proof[1], pair(proof[2], encode_proof(proof[3]))) + 5
    raise ValueError('Unknown certificate node')


def decode_certificate(n: int) -> dict[str, Any]:
    matrices, proof = unpair(n)
    return {'matrices': [decode_matrix(m) for m in decode_list(matrices)],
            'proof': decode_proof(proof)}


def encode_certificate(certificate: dict) -> int:
    if set(certificate) != {'matrices', 'proof'}:
        raise ValueError('Refutation certificates cannot contain a theorem field')
    return pair(encode_list([encode_matrix(m) for m in certificate['matrices']]),
                encode_proof(certificate['proof']))


def accepts(n: int) -> bool:
    if type(n) is not int or n < 0:
        raise ValueError('A certificate code must be a nonnegative integer')
    try:
        result = check_certificate(decode_certificate(n))
    except (ValueError, IndexError, KeyError):
        return False
    # Resource exhaustion is deliberately not caught or interpreted as success.
    return result.get('valid') is True and result.get('refutation') is True


def search() -> int:
    for n in itertools.count():
        if accepts(n):
            return n
    raise AssertionError('Unreachable with unbounded natural enumeration')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, help='Run only a finite diagnostic prefix')
    args = parser.parse_args()
    if args.limit is None:
        n = search()
        print(json.dumps({'refutation_code': n, 'certificate': decode_certificate(n)}))
        return
    if args.limit < 0:
        parser.error('--limit must be nonnegative')
    for n in range(args.limit):
        if accepts(n):
            print(json.dumps({'refutation_code': n, 'certificate': decode_certificate(n)}))
            return
    print(json.dumps({'diagnostic_prefix_checked': args.limit,
                      'refutation_found': False,
                      'scope': 'A finite check gives no consistency conclusion'}))


if __name__ == '__main__':
    main()
