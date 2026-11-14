#!/usr/bin/env python3
"""Arithmetic certificates for an every-other-candidate PA scheduler.

This checks exact numerical identities and an exhaustive finite family of
prefixes. The accompanying written induction is the universal proof; these
computations are not advertised as an exhaustive test of all proof words.
No third-party packages are needed.
"""
from itertools import product
from math import isqrt
import json


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def decode(n):
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def encode_command(c, tail):
    if c[0] == 'S':
        return pair(0, tail)
    if c[0] == 'MP':
        return pair(1, pair(c[1], tail))
    if c[0] == 'AX':
        return pair(c[1] + 2, pair(c[3], pair(c[2], tail)))
    raise ValueError(c)


def encode_word(cs, tail):
    for c in reversed(cs):
        tail = encode_command(c, tail) + 1
    return tail


def parse(n):
    a, b = decode(n)
    if a == 0:
        return ('S',), b
    if a == 1:
        offset, rest = decode(b)
        return ('MP', offset), rest
    y, rest = decode(b)
    x, rest = decode(rest)
    return ('AX', a - 2, x, y), rest


def prefix(candidate, size):
    out = []
    n = candidate
    for j in range(size):
        c, rest = parse(n)
        out.append(c)
        if j + 1 < size:
            assert rest > 0
            n = rest - 1
    return out


def depth(cs):
    return sum({'S': 1, 'MP': 2, 'AX': 3}[c[0]] for c in cs)


def progression_candidate(cs, initial_n=2):
    """Return a candidate >= initial_n in its parity class containing cs.

    Full integer encoding grows rapidly. This function intentionally remains
    a direct definition, appropriate to short arithmetic certificates.
    """
    assert cs and initial_n >= 0
    t = initial_n + 1
    d = depth(cs)
    a = encode_word(cs, t) - 1
    b = encode_word(cs, t + (1 << d)) - 1
    assert (b - a) % 2 == 1
    n = a if a % 2 == initial_n % 2 else b
    assert n >= initial_n and (n - initial_n) % 2 == 0
    assert prefix(n, len(cs)) == list(cs)
    return n


def verify():
    commands = [('S',), ('MP', 0), ('MP', 1), ('AX', 0, 0, 0),
                ('AX', 1, 1, 0), ('AX', 0, 0, 1)]
    cases = 0
    max_bits = 0
    for length in (1, 2, 3):
        for cs in product(commands, repeat=length):
            for initial_n in (0, 1, 2, 3, 4, 7):
                n = progression_candidate(cs, initial_n)
                max_bits = max(max_bits, n.bit_length())
                cases += 1
    identity_cases = 0
    for a, x, k, odd in product(range(5), range(5), range(1, 6), (1, 3, 5)):
        h = (1 << k) * odd
        diff = pair(a, x + h) - pair(a, x)
        factor = odd * (2*a + 2*x + h + 3)
        assert factor % 2 == 1
        assert diff == (1 << (k-1)) * factor
        identity_cases += 1
    receipt = {
        'checked_prefix_cases': cases,
        'checked_pair_difference_identities': identity_cases,
        'largest_candidate_bits': max_bits,
        'pair_depth_per_command': {'Shift':1, 'MP':2, 'AX':3},
        'proof_scope': 'finite arithmetic tests supporting the written universal induction',
        'result': 'PASS'
    }
    print(json.dumps(receipt, indent=2))
    return receipt


if __name__ == '__main__':
    verify()
