"""Standalone checker for the raw native calculus with determined DI witnesses.

The eight rules are Hyp, I0, IS, Tr1, QE, DE, DI*, and QI-progress.
No normalization, derived-rule oracle, or trusted theorem library is used.
See FORMAT.txt for the JSON grammar.  Python 3.10 or later is sufficient.
"""
import json
import sys


def need(condition):
    if not condition:
        raise ValueError('invalid certificate')


def valid(a, scope, depth=0, formula=False):
    if type(a) is int:
        return not formula and -scope <= a <= depth
    if type(a) is not list or not a:
        return False
    tag, *args = a
    if formula:
        if tag == '=' and len(args) == 2:
            return all(valid(t, scope, depth) for t in args)
        return tag in ('q', 'd') and len(args) == 1 and valid(
            args[0], scope, depth + (1 if tag == 'q' else 2), True)
    if tag == 's' and len(args) == 1:
        return valid(args[0], scope, depth)
    return tag == 'i' and len(args) == 3 and all(
        valid(t, scope, depth + (j == 2)) for j, t in enumerate(args))


def walk(a, action, depth=0):
    if type(a) is int:
        return action(a, depth)
    tag, *args = a
    return [tag] + [walk(t, action, depth + (
        2 if tag == 'd' else int(tag == 'q' or tag == 'i' and j == 2)))
        for j, t in enumerate(args)]


def shift(a, amount):
    return walk(a, lambda i, d: i + amount if i > d else i)


def sub(a, t, index=1):
    return walk(a, lambda i, d: shift(t, d) if i == index + d
                else i - int(i > index + d))


def infer(p, context, scope):
    need(type(p) is list and p)
    match p:
        case ['hyp', j]:
            need(type(j) is int and 0 <= j < len(context))
            out = context[j]
        case ['zero', a, h]:
            need(valid(a, scope) and valid(h, scope, 1))
            out = ['=', ['i', 0, a, h], a]
        case ['succ', n, a, h]:
            need(valid(n, scope) and valid(a, scope) and valid(h, scope, 1))
            out = ['=', ['i', ['s', n], a, h], sub(h, ['i', n, a, h])]
        case ['tr', h, p0, p1]:
            need(valid(h, scope, 1))
            e = infer(p0, context, scope)
            f = infer(p1, context, scope)
            need(e[0] == f[0] == '=' and f[1] == sub(h, e[1]))
            out = ['=', f[2], sub(h, e[2])]
        case ['qe', t, p0, p1]:
            need(valid(t, scope))
            q = infer(p0, context, scope)
            need(q[0] == 'q' and infer(p1, context, scope) == sub(q[1], 0))
            out = sub(q[1], t)
        case ['de', p0, p1]:
            q = infer(p0, context, scope)
            need(q[0] == 'd')
            body = sub(q[1], -scope - 1, 2)
            out = infer(p1, context + [['q', body]], scope + 1)
        case ['di', matrix, p0]:
            need(valid(['d', matrix], scope, formula=True))
            body = sub(matrix, -scope, 2)
            z = -scope - 1
            need(infer(p0, context + [sub(body, 0)], scope + 1)
                 == sub(body, ['s', z]))
            out = ['d', matrix]
        case ['qi', equation, p0]:
            need(valid(equation, scope, 1, True) and equation[0] == '=')
            z = -scope - 1
            need(infer(p0, context + [sub(equation, z)], scope + 1)
                 == sub(equation, ['s', z]))
            out = ['q', equation]
        case _:
            need(False)
    need(valid(out, scope, formula=True))
    return out


def check(data):
    need(type(data) is dict and set(data) == {'scope', 'context', 'goal', 'proof'})
    n, g = data['scope'], data['context']
    need(type(n) is int and n >= 0 and type(g) is list)
    need(all(valid(a, n, formula=True) for a in g))
    need(valid(data['goal'], n, formula=True))
    need(infer(data['proof'], g, n) == data['goal'])


if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
        print('ACCEPT')
    except Exception:
        print('REJECT')
        sys.exit(1)
