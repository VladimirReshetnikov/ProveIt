#!/usr/bin/env python3
"""Exact base-3 syntax audit, including the runtime's code-0 truth alias.

Original reference code for this report. Standard library only.
No claim of a verified proof-search implementation or compiler is made.
Tuples: ('top',), ('mem', i, j), ('imp', A, B), ('all', i, A).
The only normalization collapses Imp(Top, Top), recursively, to Top.
"""

from functools import lru_cache
from math import isqrt
import json
import random
import sys

if not __debug__:
    raise SystemExit('Run without -O: this audit requires Python assertions.')

TOP = ('top',)


def nat(x):
    if type(x) is not int or x < 0:
        raise ValueError('expected a nonnegative integer, excluding bool')
    return x


def pair(a, b):
    nat(a); nat(b)
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    nat(n)
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def validate(f):
    if not isinstance(f, tuple) or not f:
        raise ValueError('formula must be a nonempty tuple')
    if f == TOP:
        return
    if f[0] == 'mem' and len(f) == 3:
        nat(f[1]); nat(f[2]); return
    if f[0] == 'imp' and len(f) == 3:
        validate(f[1]); validate(f[2]); return
    if f[0] == 'all' and len(f) == 3:
        nat(f[1]); validate(f[2]); return
    raise ValueError('unknown or malformed formula')


def normalize(f):
    validate(f)
    if f == TOP or f[0] == 'mem':
        return f
    if f[0] == 'all':
        return ('all', f[1], normalize(f[2]))
    a, b = normalize(f[1]), normalize(f[2])
    return TOP if a == b == TOP else ('imp', a, b)


def encode(f):
    validate(f)
    if f == TOP:
        return 0
    if f[0] == 'mem':
        return 3 * pair(f[1], f[2]) + 1
    if f[0] == 'imp':
        return 3 * pair(encode(f[1]), encode(f[2]))
    return 3 * pair(f[1], encode(f[2])) + 2


@lru_cache(maxsize=100000)
def decode(n):
    nat(n)
    if n == 0:
        return TOP
    q, tag = divmod(n, 3)
    a, b = unpair(q)
    if tag == 0:
        if not (a < n and b < n):
            raise AssertionError('descent failed')
        return ('imp', decode(a), decode(b))
    if tag == 1:
        return ('mem', a, b)
    if not b < n:
        raise AssertionError('descent failed')
    return ('all', a, decode(b))


def labels(f):
    if f == TOP:
        return set()
    if f[0] == 'mem':
        return {f[1], f[2]}
    if f[0] == 'imp':
        return labels(f[1]) | labels(f[2])
    return {f[1]} | labels(f[2])


def evaluate(f, domain, relation, env):
    if f == TOP:
        return True
    if f[0] == 'mem':
        return relation(env.get(f[1], 0), env.get(f[2], 0))
    if f[0] == 'imp':
        return not evaluate(f[1], domain, relation, env) or evaluate(f[2], domain, relation, env)
    return all(evaluate(f[2], domain, relation, env | {f[1]: x}) for x in domain)


def run_audit():
    count = 65536
    for n in range(count):
        a, b = unpair(n)
        assert pair(a, b) == n
        f = decode(n)
        assert encode(f) == n
        assert normalize(f) == f
        assert all(i < n for i in labels(f))
    rng = random.Random(20261016)
    for _ in range(400):
        n = rng.getrandbits(rng.randrange(1, 1025))
        f = decode(n)
        assert encode(f) == n
        assert all(i < n for i in labels(f))
    def rand_formula(depth):
        if depth == 0:
            return TOP if rng.randrange(3) == 0 else ('mem', rng.randrange(4), rng.randrange(4))
        op = rng.randrange(4)
        if op < 2:
            return rand_formula(0)
        if op == 2:
            return ('imp', rand_formula(depth-1), rand_formula(depth-1))
        return ('all', rng.randrange(4), rand_formula(depth-1))
    for _ in range(1000):
        f = rand_formula(5)
        g = normalize(f)
        assert decode(encode(f)) == g
        assert encode(g) == encode(f)
        assert normalize(g) == g
        relation_code = rng.randrange(16)
        rel = lambda x, y: bool(relation_code & (1 << (2*x + y)))
        env = {i: rng.randrange(2) for i in range(4)}
        assert evaluate(f, range(2), rel, env) == evaluate(g, range(2), rel, env)
    for bad in (-1, True, 1.0, None, '1'):
        try:
            decode(bad)
        except ValueError:
            pass
        else:
            raise AssertionError(('accepted invalid code', bad))
    assert encode(('imp', TOP, TOP)) == encode(TOP) == 0
    assert decode(1) == ('mem', 0, 0)
    return {
        'natural_codes_exhaustively_checked': count,
        'random_large_codes_checked': 400,
        'random_formula_and_semantic_checks': 1000,
        'maximum_random_code_bits': 1024,
        'decode_encode_law': 'decode(encode(A)) = normalize(A)',
        'encode_decode_law': 'encode(decode(n)) = n',
        'freshness_law': 'all labels in decode(n) are strictly below n',
        'normalization': 'only Imp(Top,Top) is collapsed, recursively',
        'target_code_1': 'Mem(0,0), NOT genuine falsity',
        'proof_status': 'ordinary proofs in report; executable regressions, no proof-assistant certificate',
        'passed': True,
    }


if __name__ == '__main__':
    result = run_audit()
    text = json.dumps(result, indent=2) + '\n'
    if len(sys.argv) == 2:
        from pathlib import Path
        Path(sys.argv[1]).write_text(text)
    print(text, end='')
