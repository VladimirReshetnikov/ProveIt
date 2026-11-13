"""Shift canonical guarded certificate coordinates by two.

This is an untrusted certificate converter, never imported by the checker.
The source root packet is [A,0]; preceding instructions have four fields.
On canonical inputs every positive integer is a bound/hole coordinate.
Numerical zero and negative eigenparameter names remain unchanged.
No preservation theorem is asserted for arbitrary malformed raw inputs.
"""
import json


def shift_tree(tree):
    if type(tree) is int:
        return tree + 2 if tree > 0 else tree
    if type(tree) is list:
        return [shift_tree(child) for child in tree]
    raise ValueError('Expected a finite exact-integer/list tree')


def shift_certificate(certificate):
    if type(certificate) is not list or not certificate:
        raise ValueError('Expected a nonempty certificate stack')
    root = certificate[-1]
    if type(root) is not list or len(root) != 2 or type(root[1]) is not int or root[1] != 0:
        raise ValueError('Expected root packet [A,0]')
    shifted = []
    for packet in certificate[:-1]:
        if type(packet) is not list or len(packet) != 4:
            raise ValueError('Expected four-field instruction')
        target = shift_tree(packet)
        if packet[0] == []:
            target[0] = 0
        shifted.append(target)
    shifted.append([shift_tree(root[0]), 0])
    return shifted


if __name__ == '__main__':
    print(json.dumps(shift_certificate(json.load(open(0))), separators=(',', ':')))
