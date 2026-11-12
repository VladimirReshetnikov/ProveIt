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

def verify(a, p, g, n):
    formula(a, n)
    match p:
        case ['hyp', i]:
            require(type(i) is int and 0 <= i < len(g) and (a == g[i]))
        case []:
            match a:
                case ['=', ['i', ['s', c], b, h], r]:
                    require(r == sub(h, ['i', c, b, h]))
                case _:
                    raise ValueError('Invalid computation')
        case ['qe', b, t, p, q]:
            term(t, n)
            verify(['q', b], p, g, n)
            verify(sub(b, ['z']), q, g, n)
            require(a == sub(b, t))
        case ['de', b, p, q]:
            verify(['d', b], p, g, n)
            verify(shift(a), q, [['q', b]] + [shift(x) for x in g], n + 1)
        case ['di', t, p]:
            require(a[0] == 'd')
            term(t, n)
            b = sub(['q', a[1]], t)[1]
            h = b if b[0] == '=' and t == ['z'] else shift(sub(b, ['z']))
            verify(sub(b, ['s', ['v', 0]], 0), p, [h] + [shift(x) for x in g], n + 1)
        case ['tr', h, s, t, p, q]:
            term(h, n + 1)
            require(a[0] == '=')
            verify(['=', s, t], p, g, n)
            verify(['=', sub(h, s), a[1]], q, g, n)
            require(a[2] == sub(h, t))
        case _:
            raise ValueError('Invalid proof')

def check(c):
    require(type(c) is dict and set(c) == {'variables', 'context', 'goal', 'proof'})
    n, g, a, p = (c[k] for k in ['variables', 'context', 'goal', 'proof'])
    require(type(n) is int and n >= 0 and (type(g) is list))
    for b in g:
        formula(b, n)
    verify(a, p, g, n)
if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
    except (ValueError, TypeError, IndexError, KeyError, RecursionError):
        sys.exit(1)
    print('ACCEPT')
