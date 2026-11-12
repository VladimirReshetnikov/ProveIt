import json
import sys

def require(condition):
    if not condition:
        raise ValueError('Invalid certificate')

def term(a, n):
    match a:
        case ['v', i]:
            require(type(i) is int and 0 <= i < n)
        case ['z']:
            pass
        case ['s', b]:
            term(b, n)
        case ['i', c, b, h]:
            require(c != ['z'])
            term(c, n)
            term(b, n)
            term(h, n + 1)
        case _:
            raise ValueError('Invalid term')

def formula(a, n):
    match a:
        case ['=', s, t]:
            term(s, n)
            term(t, n)
        case ['q', b]:
            formula(b, n + 1)
        case ['d', b]:
            formula(b, n + 2)
        case _:
            raise ValueError('Invalid formula')

def walk(a, f, d=0):
    if a[0] == 'v':
        return f(a[1], d)
    a = [a[0]] + [walk(b, f, d + {'i': [0, 0, 1], 'q': [1], 'd': [2]}.get(a[0], [0] * len(a))[j]) for j, b in enumerate(a[1:])]
    return a[2] if a[:2] == ['i', ['z']] else a

def shift(a, k=1):
    return walk(a, lambda i, d: ['v', i + k if i >= d else i])

def sub(a, t, drop=1):
    return walk(a, lambda i, d: ['v', i] if i < d else shift(t, d) if i == d else ['v', i - drop])

def infer(p, g, n):
    match p:
        case ['hyp', i]:
            require(type(i) is int and 0 <= i < len(g))
            return g[i]
        case ['succ', c, a, h]:
            term(c, n)
            term(a, n)
            term(h, n + 1)
            return ['=', ['i', ['s', c], a, h], sub(h, ['i', c, a, h])]
        case ['qe', t, p, q]:
            term(t, n)
            a = infer(p, g, n)
            require(a[0] == 'q')
            require(infer(q, g, n) == sub(a[1], ['z']))
            return sub(a[1], t)
        case ['de', a, p, q]:
            formula(a, n)
            b = infer(p, g, n)
            require(b[0] == 'd')
            require(infer(q, [['q', b[1]]] + [shift(x) for x in g], n + 1) == shift(a))
            return a
        case ['di', b, t, p]:
            formula(b, n + 2)
            term(t, n)
            a = sub(['q', b], t)[1]
            h = shift(sub(a, ['z']))
            require(infer(p, [a if h[1:2] == h[2:] else h] + [shift(x) for x in g], n + 1) == sub(a, ['s', ['v', 0]], 0))
            return ['d', b]
        case ['tr', a, p, q]:
            term(a, n + 1)
            e = infer(p, g, n)
            f = infer(q, g, n)
            require(e[0] == f[0] == '=' and f[1] == sub(a, e[1]))
            return ['=', f[2], sub(a, e[2])]
        case _:
            raise ValueError('Invalid proof')

def check(c):
    require(type(c) is dict and set(c) == {'variables', 'context', 'goal', 'proof'})
    n, g, a, p = (c[k] for k in ['variables', 'context', 'goal', 'proof'])
    require(type(n) is int and n >= 0 and (type(g) is list))
    for b in g:
        formula(b, n)
    formula(a, n)
    require(infer(p, g, n) == a)
if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
    except (ValueError, TypeError, IndexError, KeyError, RecursionError):
        sys.exit(1)
    print('ACCEPT')
