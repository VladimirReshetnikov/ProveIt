#!/usr/bin/env python3
"""Independent local-rule checker for a positive canonical MIX derivation.

No membership search, symmetry reduction, interval extraction, or theorem about
families is used here. Each node is verified against the three defining rules.
This checks positive certificates, not the exhaustive negative decisions.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def check_certificate(data: dict) -> tuple[str, ...]:
    if data.get('format') != 'canonical-mix-derivation-v1':
        raise ValueError('Unrecognized certificate format.')
    r = data.get('arity')
    if type(r) is not int or r < 1:
        raise ValueError('Invalid arity.')
    computed: list[tuple[str, ...]] = []

    def child(index, current):
        if type(index) is not int or not 0 <= index < current:
            raise ValueError('Children must reference earlier nodes.')
        return computed[index]

    for i, node in enumerate(data['nodes']):
        rule = node.get('rule')
        if rule == 'empty':
            value = ('',) * r
        elif rule == 'wrap':
            before = child(node['child'], i)
            left, right = node['left'], node['right']
            if len(left) != r or len(right) != r:
                raise ValueError('Wrong number of endpoint slots.')
            if any(type(s) is not str or s not in ('', 'a', 'b', 'c')
                   for s in left + right):
                raise ValueError('Each endpoint must insert zero or one letter.')
            if sorted(''.join(left + right)) != list('abc'):
                raise ValueError('A wrap must insert exactly one a, b and c.')
            value = tuple(left[j] + before[j] + right[j] for j in range(r))
        elif rule == 'combine':
            outer = child(node['outer'], i)
            inner = child(node['inner'], i)
            gap, cuts = node['gap'], node['cuts']
            if type(gap) is not int or not 0 <= gap <= r:
                raise ValueError('Invalid insertion gap.')
            if (len(cuts) != r + 1 or any(type(c) is not int for c in cuts)
                    or cuts[0] != 0 or cuts[-1] != 2*r
                    or any(a > b for a, b in zip(cuts, cuts[1:]))):
                raise ValueError('Invalid regrouping cuts.')
            sequence = outer[:gap] + inner + outer[gap:]
            value = tuple(''.join(sequence[cuts[j]:cuts[j+1]]) for j in range(r))
        else:
            raise ValueError('Unknown rule.')
        if list(value) != node.get('tuple'):
            raise ValueError(f'Claimed tuple differs at node {i}.')
        computed.append(value)
    root = data['root']
    if type(root) is not int or not 0 <= root < len(computed):
        raise ValueError('Invalid root.')
    result = computed[root]
    if data.get('word') != ''.join(result):
        raise ValueError('Claimed root word differs.')
    return result


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('certificate', type=Path)
    args = cli.parse_args()
    try:
        data = json.loads(args.certificate.read_text())
        root = check_certificate(data)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        cli.exit(1, f'INVALID: {exc}\n')
    print(json.dumps({'valid': True, 'arity': data['arity'],
                      'nodes': len(data['nodes']), 'root_tuple': root}, indent=2))

if __name__ == '__main__':
    main()
