"""Untrusted producer translating tagged clausal certificates to arity syntax."""
import json
import sys


def term(a, scope, depth=0):
    if type(a) is int:
        return a if a <= depth else a - depth - scope - 1
    return [term(a[0], scope, depth), term(a[1], scope, depth),
            term(a[2], scope, depth + 1)]


def formula(a, scope, depth=0):
    if a[0] == '=':
        return [term(a[1], scope, depth), term(a[2], scope, depth)]
    if a[0] != 'D':
        raise ValueError('only Eq/D formulas are accepted')
    return [formula(a[1], scope, depth + 2)]


def proof(p, scope=0):
    tag = p[0]
    if tag == 'u':
        return [tag, p[1], term(p[2], scope), proof(p[3], scope)]
    if tag == 'r':
        return [tag, term(p[1], scope), term(p[2], scope), term(p[3], scope, 1)]
    if tag == 'x':
        return [tag, term(p[1], scope, 1), proof(p[2], scope), proof(p[3], scope)]
    if tag == 'e':
        return [tag, formula(p[1], scope), proof(p[2], scope), proof(p[3], scope + 1)]
    if tag == 'i':
        return [tag, formula(p[1], scope), term(p[2], scope), proof(p[3], scope + 1)]
    raise ValueError('unknown instruction')


def translate(certificate):
    return {'goal': formula(certificate['goal'], 0),
            'proof': proof(certificate['proof'])}


if __name__ == '__main__':
    json.dump(translate(json.load(sys.stdin)), sys.stdout)
    print()
