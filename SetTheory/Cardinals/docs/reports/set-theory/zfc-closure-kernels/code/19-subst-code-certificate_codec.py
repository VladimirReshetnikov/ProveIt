#!/usr/bin/env python3
"""Total natural-number certificate syntax and bounded diagnostic search.

Every recursive decode uses a smaller natural. Scope, map validity, and rule
applicability are checked afterwards by lazy_psc.check. Encoding collisions do
not exist in these syntax families. The list/matrix/proof trees are finite.
This is a mathematical search specification implemented in ordinary Python;
host memory/recursion failures are never treated as successful refutations.
"""
from __future__ import annotations

import argparse
import json
from math import isqrt
from pathlib import Path
import lazy_psc as logic


def pair(a, b):
    a, b = logic.nat(a), logic.nat(b)
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    n = logic.nat(n)
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def encode_list(items):
    out = 0
    for item in reversed(items):
        out = 1 + pair(item, out)
    return out


def decode_list(n):
    logic.nat(n)
    out = []
    while n:
        head, n = unpair(n - 1)
        out.append(head)
    return out


def decode_term(n):
    return ('f' if n % 2 == 0 else 'b', n // 2)


def encode_term(t):
    return 2 * t[1] + (t[0] == 'b')


def decode_formula(n):
    logic.nat(n)
    if n == 0:
        return logic.BOT
    q, tag = divmod(n - 1, 3)
    if tag == 2:
        return 'A', decode_formula(q)
    a, b = unpair(q)
    if tag == 0:
        return 'R', decode_term(a), decode_term(b)
    return 'I', decode_formula(a), decode_formula(b)


def encode_formula(f):
    if f[0] == 'B':
        return 0
    if f[0] == 'R':
        return 1 + 3 * pair(encode_term(f[1]), encode_term(f[2]))
    if f[0] == 'I':
        return 2 + 3 * pair(encode_formula(f[1]), encode_formula(f[2]))
    if f[0] == 'A':
        return 3 + 3 * encode_formula(f[1])
    raise ValueError('Not source formula syntax')


def decode_proof(n):
    logic.nat(n)
    q, tag = divmod(n, 7)
    if tag == 1:
        return ['B', q]
    i, payload = unpair(q)
    if tag == 0:
        return ['X', i, payload]
    if tag == 2:
        return ['I-', i, decode_proof(payload)]
    if tag == 4:
        return ['A-', i, decode_proof(payload)]
    a, b = unpair(payload)
    if tag == 3:
        return ['I+', i, decode_proof(a), decode_proof(b)]
    if tag == 5:
        return ['A+', i, a, decode_proof(b)]
    return ['AX', i, [list(unpair(x)) for x in decode_list(a)], decode_proof(b)]


def encode_proof(p):
    op = p[0]
    if op == 'X':
        return 7 * pair(p[1], p[2])
    if op == 'B':
        return 7 * p[1] + 1
    if op == 'I-':
        return 7 * pair(p[1], encode_proof(p[2])) + 2
    if op == 'A-':
        return 7 * pair(p[1], encode_proof(p[2])) + 4
    if op == 'I+':
        return 7 * pair(p[1], pair(encode_proof(p[2]), encode_proof(p[3]))) + 3
    if op == 'A+':
        return 7 * pair(p[1], pair(p[2], encode_proof(p[3]))) + 5
    if op == 'AX':
        env = encode_list([pair(k, v) for k, v in p[2]])
        return 7 * pair(p[1], pair(env, encode_proof(p[3]))) + 6
    raise ValueError('Unknown proof instruction')


def decode(n):
    matrices, proof = unpair(n)
    return {'matrices': [decode_formula(x) for x in decode_list(matrices)],
            'proof': decode_proof(proof)}


def encode(certificate):
    return pair(encode_list([encode_formula(m) for m in certificate['matrices']]),
                encode_proof(certificate['proof']))


def accepts(n):
    try:
        result = logic.check(decode(n))
    except ValueError:
        return False
    return result['valid'] and result['refutation']


def search(limit=None):
    """limit=None is the unbounded mathematical loop. CLI requires a limit."""
    n = 0
    while limit is None or n < limit:
        if accepts(n):
            return {'accepted_refutation': True, 'certificate_code': n}
        n += 1
    return {'accepted_refutation': False, 'checked': n,
            'status': 'bounded diagnostic finished; no consistency claim'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, required=True,
                        help='Finite diagnostic only; must be nonnegative')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    logic.nat(args.limit)
    result = search(args.limit)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
