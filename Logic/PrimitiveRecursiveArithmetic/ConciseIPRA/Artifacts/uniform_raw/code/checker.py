"""Uniform newest-parameter introduction for raw guarded iPRA.

Terms: 0, positive de Bruijn indices, negative free-parameter levels,
[0,t] (successor), [n,a,h] (iteration; h binds one variable).
Formulas: [s,t] (equation), [B] (D; B binds x then y).
Proof packets and the mathematical contract are documented in FORMAT.txt.
"""
import json
import sys


def need(condition):
    if not condition:
        raise ValueError('invalid certificate')


def term(a, scope, depth=0):
    if type(a) is int:
        return -scope <= a <= depth
    if type(a) is not list:
        return False
    if len(a) == 2:
        return type(a[0]) is int and a[0] == 0 and term(a[1], scope, depth)
    return len(a) == 3 and term(a[0], scope, depth) and term(a[1], scope, depth) and term(a[2], scope, depth + 1)


def formula(a, scope, depth=0):
    if type(a) is not list:
        return False
    if len(a) == 2:
        return all(term(b, scope, depth) for b in a)
    if len(a) != 1 or not formula(a[0], scope, depth + 2):
        return False
    b = a[0]
    return len(b) == 1 or all(type(t) is list and len(t) == 3 and t[:2] == [1, 0] for t in b)


def binding(a, index):
    return 2 if len(a) == 1 else int(len(a) == 3 and index == 2)


def shift(a, amount, depth=0):
    if type(a) is int:
        return a + amount if a > depth else a
    return [shift(b, amount, depth + binding(a, i)) for i, b in enumerate(a)]


def sub(a, value, index=1, depth=0):
    if type(a) is int:
        if a == index + depth:
            return shift(value, depth)
        return a - 1 if a > index + depth else a
    return [sub(b, value, index, depth + binding(a, i)) for i, b in enumerate(a)]



H = [[0, 0, 0], 0]


def infer(proof, clauses=(), scope=0):
    need(type(proof) is list and len(proof) > 0)
    tag = proof[0]
    if tag == 'zero':
        need(len(proof) == 3)
        a, h = proof[1:]
        need(term(a, scope) and term(h, scope, 1))
        out = [[0, a, h], a]
    elif tag == 'succ':
        need(len(proof) == 4)
        n, a, h = proof[1:]
        need(term(n, scope) and term(a, scope) and term(h, scope, 1))
        out = [[[0, n], a, h], sub(h, [n, a, h])]
    elif tag == 'use':
        need(len(proof) == 4)
        j, t, p = proof[1:]
        need(type(j) is int and 0 <= j < len(clauses) and term(t, scope))
        a, body = clauses[j]
        need(infer(p, clauses, scope) == a)
        out = sub(body, t)
    elif tag == 'tr':
        need(len(proof) == 4)
        template, p, q = proof[1:]
        need(formula(template, scope, 1))
        equation = infer(p, clauses, scope)
        need(len(equation) == 2)
        s, t = equation
        need(infer(q, clauses, scope) == sub(template, s))
        out = sub(template, t)
    elif tag == 'open':
        need(len(proof) == 3)
        major = infer(proof[1], clauses, scope)
        need(len(major) == 1)
        body = sub(major[0], -scope - 1, 2)
        out = infer(proof[2], clauses + ((sub(body, 0), body),), scope + 1)
    elif tag == 'intro':
        need(len(proof) == 3)
        matrix, p = proof[1:]
        need(formula([matrix], scope))
        t = -scope
        z = -scope - 1
        body = sub(matrix, t, 2)
        base = sub(body, z if len(matrix) == 2 else 0)
        need(infer(p, clauses + ((H, base),), scope + 1) == sub(body, [0, z]))
        out = [matrix]
    else:
        raise ValueError('unknown instruction')
    need(formula(out, scope))
    return out


def check(data):
    need(type(data) is dict and set(data) == {'goal', 'proof'})
    need(formula(data['goal'], 0))
    need(infer(data['proof']) == data['goal'])


if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
        print('ACCEPT')
    except Exception:
        print('REJECT')
        sys.exit(1)
