"""Bijection between shared-leaf packets and argument-bound packets.

The transformation is untrusted. Both checkers verify their own packets.
Only the final two root records are combined; nested records are unchanged.
"""
import json
import sys


def forward(certificate):
    header = certificate[-1]
    packet = certificate[-2]
    if type(header) is not list or len(header) != 2:
        raise ValueError('Expected [goal, scope] as the old root header')
    if type(packet) is not list or len(packet) != 4:
        raise ValueError('Expected four fields in the first root packet')
    return certificate[:-2] + [header + packet]


def backward(certificate):
    header = certificate[-1]
    if type(header) is not list or len(header) != 6:
        raise ValueError('Expected [goal, scope, major, source, seed, body]')
    return certificate[:-1] + [header[2:], header[:2]]


if __name__ == '__main__':
    convert = backward if '--backward' in sys.argv else forward
    json.dump(convert(json.load(sys.stdin)), sys.stdout, separators=(',', ':'))
    print()
