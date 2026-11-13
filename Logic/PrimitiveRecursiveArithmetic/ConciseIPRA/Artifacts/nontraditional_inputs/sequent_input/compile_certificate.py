"""Translate a closed-theorem certificate to the empty-context sequent format.

The translator is untrusted convenience code; only checker_sequent458.py
determines acceptance. The old packet list is preserved without reordering.
"""
import json
import sys


def translate(proof):
    if type(proof) is not list or not proof:
        raise ValueError('Expected a nonempty JSON stack')
    header = proof[-1]
    if type(header) is not list or len(header) != 2:
        raise ValueError('Expected final header [goal, 0]')
    goal, floor = header
    if type(floor) is not int or floor != 0:
        raise ValueError('This translator handles closed theorems at floor 0')
    return proof[:-1] + [[[], goal, 0]]


if __name__ == '__main__':
    json.dump(translate(json.load(sys.stdin)), sys.stdout, separators=(',', ':'))
    print()
