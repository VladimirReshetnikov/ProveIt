#!/usr/bin/env python3
"""Construct actual A_3 derivations of (a^p, v, a^(N-p)).

The JSON uses ONLY the original empty, wrap, and binary-regroup rules.
It does not ask the backward parser whether a tuple is derivable.
"""
from __future__ import annotations
import argparse
import json


def build_certificate(v: str, p: int) -> dict:
    if any(c not in 'bc' for c in v) or v.count('b') != v.count('c'):
        raise ValueError('v must have equally many b and c and no other letters.')
    n = len(v) // 2
    if not 0 <= p <= n:
        raise ValueError('p must lie between zero and the number of b letters.')
    nodes: list[dict] = []

    def emit(node: dict) -> int:
        nodes.append(node)
        return len(nodes) - 1

    def derive(v: str, p: int) -> int:
        n = len(v) // 2
        target = ['a' * p, v, 'a' * (n - p)]
        if not v:
            return emit({'rule': 'empty', 'tuple': target})
        balance = 0
        first_return = None
        for i, c in enumerate(v, 1):
            balance += 1 if c == 'b' else -1
            if balance == 0:
                first_return = i
                break
        assert first_return is not None
        if first_return == len(v):
            assert v[0] != v[-1]
            child = derive(v[1:-1], p-1 if p else 0)
            left, right = ['', v[0], ''], ['', v[-1], '']
            if p:
                left[0] = 'a'
            else:
                right[2] = 'a'
            return emit({'rule': 'wrap', 'child': child, 'left': left,
                         'right': right, 'tuple': target})
        v1, v2 = v[:first_return], v[first_return:]
        n1 = len(v1) // 2
        if p <= n1:
            outer = derive(v1, p)
            inner = derive(v2, 0)
            gap, cuts = 2, [0, 1, 4, 6]
        else:
            outer = derive(v2, p-n1)
            inner = derive(v1, n1)
            gap, cuts = 1, [0, 2, 5, 6]
        return emit({'rule': 'combine', 'outer': outer, 'inner': inner,
                     'gap': gap, 'cuts': cuts, 'tuple': target})

    root = derive(v, p)
    return {'format': 'canonical-mix-derivation-v1', 'arity': 3,
            'root': root, 'nodes': nodes,
            'word': ''.join(nodes[root]['tuple'])}


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('v', help='A binary word with equally many b and c.')
    cli.add_argument('p', type=int, help='Number of a letters in first component.')
    args = cli.parse_args()
    try:
        certificate = build_certificate(args.v, args.p)
    except ValueError as exc:
        cli.error(str(exc))
    print(json.dumps(certificate, indent=2))

if __name__ == '__main__':
    main()
