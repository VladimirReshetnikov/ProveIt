"""Translate a canonical 473-codec certificate to the 472-codec.

Usage: python3 translate_certificate.py < old.json > shifted.json

Assumptions: the input is a canonical integer/list certificate for the
inherited guarded public calculus; the terminal packet is [A,0], all
other packets have four fields, numerical zero is0, bound coordinates
are positive integers, and eigenparameters have negative names. The
neutral major is[]. This utility does not establish that a proof is
correct or validate the full canonical grammar. Feed its output to the
standalone checker. No preservation claim is made for arbitrary raw
certificates or arbitrary noncanonical aliases.
"""
import json


def shift(tree):
    if type(tree) is int:
        return tree + 2 if tree > 0 else tree
    if type(tree) is list:
        return [shift(child) for child in tree]
    raise ValueError('Expected an exact integer/list tree')


def translate(certificate):
    if type(certificate) is not list or not certificate:
        raise ValueError('Expected a nonempty packet stack')
    terminal = certificate[-1]
    if type(terminal) is not list or len(terminal) != 2 or type(terminal[1]) is not int or terminal[1] != 0:
        raise ValueError('The terminal packet must be [A,0]')
    result = []
    for packet in certificate[:-1]:
        if type(packet) is not list or len(packet) != 4:
            raise ValueError('An instruction must have four fields')
        translated = shift(packet)
        if packet[0] == []:
            translated[0] = 0
        result.append(translated)
    result.append([shift(terminal[0]), 0])
    return result


if __name__ == '__main__':
    print(json.dumps(translate(json.load(open(0))), separators=(',', ':')))
