#!/usr/bin/env python3
"""Replay an occurrence-level associativity witness from parent195S to PA194.

Both endpoints have the same 190-token word. The intermediate trees are an
algebraic certificate only: their scanner constraints and source jump maps
are not claimed to be valid. build194.py checks the two endpoint source maps.
"""
from pathlib import Path
import hashlib
import json

import compiler as c
from build194 import expanded, word

HERE = Path(__file__).resolve().parent


def rotate(tree, path, right):
    if path:
        left, other = tree
        if path[0] == 0:
            return rotate(left, path[1:], right), other
        return left, rotate(other, path[1:], right)
    if right:
        (a, b), d = tree
        return a, (b, d)
    a, (b, d) = tree
    return (a, b), d


def normalize(tree, prefix=()):
    if not c.isnode(tree):
        return tree, []
    steps = []
    while c.isnode(tree[0]):
        tree = rotate(tree, (), True)
        steps.append(prefix)
    right, rest = normalize(tree[1], prefix + (1,))
    return (tree[0], right), steps + rest


def digest(tree):
    return hashlib.sha256(json.dumps(tree, separators=(',', ':')).encode()).hexdigest()


def main():
    if not __debug__:
        raise SystemExit('Run without Python -O.')
    parent = expanded(c.read_grammar(HERE / 'inputs/parent195S.grammar.json'))
    target = expanded(c.read_grammar(HERE / 'source/pa194.grammar.json'))
    assert word(parent) == word(target) and len(word(parent)) == 190
    parent_comb, forward = normalize(parent)
    target_comb, backward = normalize(target)
    assert parent_comb == target_comb
    moves = [(path, True) for path in forward]
    moves += [(path, False) for path in reversed(backward)]
    current = parent
    for path, right in moves:
        old_word = word(current)
        current = rotate(current, path, right)
        assert word(current) == old_word
    assert current == target
    certificate = {
        'parent_expanded_tree_sha256': digest(parent),
        'target_expanded_tree_sha256': digest(target),
        'tokens': 190, 'right_rotations': len(forward),
        'left_rotations': len(backward), 'total_rotations': len(moves),
        'moves': [{'path': ''.join(map(str, path)),
                   'direction': 'right' if right else 'left'} for path, right in moves],
        'replay_verified': True,
        'scope': 'Algebraic endpoint-tree witness; endpoint source CFG equality is checked separately.'}
    (HERE / 'evidence/pa194.rotations.json').write_text(json.dumps(certificate, indent=2) + '\n')
    print(json.dumps({key: value for key, value in certificate.items() if key != 'moves'}, indent=2))


if __name__ == '__main__':
    main()
