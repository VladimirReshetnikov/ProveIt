"""Raw iPRA proof checker with a bounded, reversible left-endpoint step.

Terms and formulas use tagged de Bruijn trees. No normalization is performed.
The only computation rule contracts one iterator, either at the root or
after at most three consecutive iterator-counter edges. All active raw hints
are checked for their sort and numerical scope before any substitution or
erasing contraction. The proof is goal-directed; hypothesis and reflexivity
leaves require a literal JSON null, also enforced in the matched control.
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


def step(a, d):
    if a[0] == 'i':
        _, n, seed, body = a
        return (['i', step(n, d - 1), seed, body] if d
                else seed if n == ['z']
                else sub(body, ['i', n[1], seed, body]) if n[0] == 's'
                else None)


def prove(a, p, g, n):
    match p:
        case None:
            require(a in g or a[0] == '=' and a[1] == a[2])
        case ['vs', j, t, u, left, right]:
            require(type(j) is int and 0 <= j < n and a[0] == '=')
            raw(t, n)
            raw(u, n)
            require(sub(u, t, 0, j) == a[2])
            prove(['=', ['v', j], t], left, g, n)
            prove(['=', u, a[1]], right, g, n)
        case ['qe', b, t, left, right]:
            raw(b, n + 1, 1)
            raw(t, n)
            require(sub(b, t) == a)
            prove(['q', b], left, g, n)
            prove(sub(b, ['z']), right, g, n)
        case ['de', b, major, branch]:
            raw(b, n + 2, 1)
            prove(['d', b], major, g, n)
            prove(shift(a), branch, [['q', b]] + [shift(x) for x in g], n + 1)
        case ['di', t, branch]:
            require(a[0] == 'd')
            raw(t, n)
            b = sub(a[1], shift(t), index=1)
            h = b if b[0] == '=' and t == ['z'] else shift(sub(b, ['z']))
            prove(sub(b, ['s', ['v', 0]], 0), branch, [h] + [shift(x) for x in g], n + 1)
        case ['hc', depth, previous, branch]:
            require(type(depth) is int and 0 <= depth <= 3 and a[0] == '=')
            raw(previous, n)
            require(step(previous, depth) == a[1] or step(a[1], depth) == previous)
            prove(['=', previous, a[2]], branch, g, n)
        case _:
            raise ValueError('Invalid proof')


def check(data):
    require(type(data) is dict and set(data) == {'variables', 'context', 'goal', 'proof'})
    n, g, a, p = (data[k] for k in ['variables', 'context', 'goal', 'proof'])
    require(type(n) is int and n >= 0 and type(g) is list)
    for b in g:
        raw(b, n, 1)
    raw(a, n, 1)
    prove(a, p, g, n)


if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
    except Exception:
        sys.exit(1)
    print('ACCEPT')
