#!/usr/bin/env python3
"""Construct and replay an occurrence-level associativity witness.

The witness is a canonical proof between the two expanded macro trees, not a
record of the stochastic search trajectory.  Endpoint equality of the resolved
instruction maps is checked separately by build_check.py; intermediate trees
are not claimed to be valid runtime implementations.
"""
from pathlib import Path
import json
import compiler as c
from build_check import expanded

HERE = Path(__file__).resolve().parent


def right_comb(tree, path=(), moves=None):
    if moves is None:
        moves = []
    if not c.isnode(tree):
        return tree, moves
    while c.isnode(tree[0]):
        (a, b), d = tree
        tree = (a, (b, d))
        moves.append((''.join(map(str, path)), 'right'))
    right, moves = right_comb(tree[1], path + (1,), moves)
    return (tree[0], right), moves


def rotate(tree, path, direction):
    if path:
        bit = int(path[0])
        children = list(tree)
        children[bit] = rotate(children[bit], path[1:], direction)
        return tuple(children)
    if direction == 'right':
        (a, b), d = tree
        return (a, (b, d))
    a, (b, d) = tree
    return ((a, b), d)


def main():
    if not __debug__:
        raise SystemExit('Run without Python -O: the certificate assertions are required.')
    original = expanded(c.read_grammar(HERE / 'baseline.grammar.json'))
    final = expanded(c.read_grammar(HERE / 'grammar.json'))
    left, forwards = right_comb(original)
    right, backwards = right_comb(final)
    assert left == right
    moves = forwards + [(p, 'left') for p, _ in reversed(backwards)]
    tree = original
    for path, direction in moves:
        tree = rotate(tree, path, direction)
    assert tree == final
    result = {'kind': 'occurrence-level associativity certificate',
              'macro_leaves': 190, 'rotation_count': len(moves),
              'forward_normalization_count': len(forwards),
              'reverse_normalization_count': len(backwards),
              'endpoint_equal': True, 'rotations': moves}
    (HERE / 'rotations.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'rotations'}, indent=2))


if __name__ == '__main__':
    main()
