import json
import sys

def require(condition):
    if not condition:
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
    a = [tag] + [walk(b, f, d + k, tag in ('q', 'd')) for b, k in zip(args, binders)]
    return a

def syntax(a, n, sort=0):

    def variable(i, d):
        require(type(i) is int and 0 <= i < n + d)
        return ['v', i]
    require(walk(a, variable, sort=sort) == a)

def shift(a, k=1):
    return walk(a, lambda i, d: ['v', i + k if i >= d else i])

def sub(a, t, drop=1):
    return walk(a, lambda i, d: ['v', i] if i < d else shift(t, d) if i == d else ['v', i - drop])

def prove(a, p, g, n):
    syntax(a, n, 1)
    if a in g:
        return
    match a:
        case ['=', ['i', ['z'], b, h], r] if r == b:
            return
        case ['=', ['i', ['s', c], b, h], r] if r == sub(h, ['i', c, b, h]):
            return
    match p:
        case ['qe', b, t, p, q]:
            syntax(t, n)
            prove(['q', b], p, g, n)
            require(a == sub(b, t))
            prove(sub(b, ['z']), q, g, n)
        case ['de', b, p, q]:
            prove(['d', b], p, g, n)
            prove(shift(a), q, [['q', b]] + [shift(x) for x in g], n + 1)
        case ['di', t, p]:
            require(a[0] == 'd')
            syntax(t, n)
            b = sub(['q', a[1]], t)[1]
            h = b if b[0] == '=' and t == ['z'] else shift(sub(b, ['z']))
            prove(sub(b, ['s', ['v', 0]], 0), p, [h] + [shift(x) for x in g], n + 1)
        case ['tr', s, t, h, p, q]:
            prove(['=', s, t], p, g, n)
            syntax(h, n + 1)
            require(a[0] == '=' and a[2] == sub(h, t))
            prove(['=', sub(h, s), a[1]], q, g, n)
        case _:
            raise ValueError('Invalid proof')

def check(c):
    require(type(c) is dict and set(c) == {'variables', 'context', 'goal', 'proof'})
    n, g, a, p = (c[k] for k in ['variables', 'context', 'goal', 'proof'])
    require(type(n) is int and n >= 0 and (type(g) is list))
    for b in g:
        syntax(b, n, 1)
    prove(a, p, g, n)
if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
    except (ValueError, TypeError, IndexError, KeyError, RecursionError):
        sys.exit(1)
    print('ACCEPT')
