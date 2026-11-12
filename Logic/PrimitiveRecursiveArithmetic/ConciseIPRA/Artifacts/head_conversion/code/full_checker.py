"""Matched control with full equality conversion and raw term hints.

Raw term hints are validated before any erasing computation. Only equation
endpoints are normalized. This is a readable checker, not the compact codec.
"""
import json
import sys


def require(value):
    if not value:
        raise ValueError('Invalid certificate')


def walk(a, f, d=0, sort=-1):
    require(type(a) is list and a)
    tag, *args = a
    require(sort < 0 or (tag in ('=', 'q', 'd')) == sort)
    if tag == 'v':
        require(len(args) == 1)
        return f(args[0], d)
    binders = {'z': [], 's': [0], 'i': [0, 0, 1], '=': [0, 0], 'q': [1], 'd': [2]}[tag]
    require(len(args) == len(binders))
    return [tag] + [walk(b, f, d + k, tag in ('q', 'd')) for b, k in zip(args, binders)]


def raw(a, n, sort=0):
    def variable(i, d):
        require(type(i) is int and 0 <= i < n + d)
        return ['v', i]
    walk(a, variable, sort=sort)


def shift(a, k=1, cutoff=0):
    return walk(a, lambda i, d: ['v', i + k if i >= d else i], cutoff)


def sub(a, t, drop=1, index=0):
    return walk(a, lambda i, d: ['v', i] if i < d + index else shift(t, d) if i == d + index else ['v', i - drop])


def normal(a):
    if a[0] in ('=', 'q', 'd'):
        return [a[0]] + [normal(b) for b in a[1:]]
    if a[0] == 'v':
        return a
    a = [a[0]] + [normal(b) for b in a[1:]]
    if a[0] != 'i':
        return a
    _, n, seed, body = a
    if n == ['z']:
        return normal(seed)
    if n[0] == 's':
        return normal(sub(body, ['i', n[1], seed, body]))
    return ['i', n, seed, body]


def formula(a, n):
    raw(a, n, 1)
    require(normal(a) == a)


def instance(a, t, drop=1, index=0):
    return normal(sub(a, t, drop, index))


def prove(a, p, g, n):
    if a in g or a[0] == '=' and a[1] == a[2]:
        return
    match p:
        case ['vs', j, t, u, left, right]:
            require(type(j) is int and 0 <= j < n and a[0] == '=')
            raw(t, n)
            raw(u, n)
            require(instance(u, t, 0, j) == a[2])
            prove(['=', ['v', j], normal(t)], left, g, n)
            prove(['=', normal(u), a[1]], right, g, n)
        case ['qe', b, t, left, right]:
            formula(b, n + 1)
            raw(t, n)
            require(instance(b, t) == a)
            prove(['q', b], left, g, n)
            prove(instance(b, ['z']), right, g, n)
        case ['de', b, major, branch]:
            formula(b, n + 2)
            prove(['d', b], major, g, n)
            prove(shift(a), branch, [['q', b]] + [shift(x) for x in g], n + 1)
        case ['di', t, branch]:
            require(a[0] == 'd')
            raw(t, n)
            b = instance(a[1], shift(t), index=1)
            h = b if b[0] == '=' and t == ['z'] else shift(instance(b, ['z']))
            prove(instance(b, ['s', ['v', 0]], 0), branch, [h] + [shift(x) for x in g], n + 1)
        case _:
            raise ValueError('Invalid proof')


def check(data):
    require(type(data) is dict and set(data) == {'variables', 'context', 'goal', 'proof'})
    n, g, a, p = (data[k] for k in ['variables', 'context', 'goal', 'proof'])
    require(type(n) is int and n >= 0 and type(g) is list)
    for b in g:
        formula(b, n)
    formula(a, n)
    prove(a, p, g, n)


if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
    except Exception:
        sys.exit(1)
    print('ACCEPT')
