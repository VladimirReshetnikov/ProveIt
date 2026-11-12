"""Native iPRA with computational equality and diagonal introduction.

Terms: 0, negative free levels, positive bound indices, [0,t] (S),
[n,a,h] (I). Formulas: [s,t] (equality), [B] (D), ['q',B] (Q).
Contexts contain formulas.
Input: {'goal': a closed formula, 'proof': a finite proof tree}.
"""
import json
import sys


def fail():
    raise ValueError('invalid certificate')


def term(a, scope, depth=0):
    if type(a) is int:
        return -scope <= a <= depth
    return (type(a) is list and len(a) in (2, 3)
            and (len(a) == 3 or a[0] == 0)
            and all(term(t, scope, depth + (len(a) == 3 and i == 2))
                    for i, t in enumerate(a)))


def formula(a, scope, depth=0):
    return (type(a) is list
            and ((len(a) == 2 and all(term(t, scope, depth) for t in a))
                 or (len(a) == 1 and formula(a[0], scope, depth + 2))
                 or (len(a) == 2 and a[0] == 'q'
                     and formula(a[1], scope, depth + 1))))


def opening(a, value, depth=0):
    if type(a) is int:
        return value if a == depth + 1 else a - (a > depth + 1)
    size = len(a)
    if size == 2 and a[0] == 'q':
        return ['q', opening(a[1], value, depth + 1)]
    return [opening(t, value, depth + (2 if size == 1 else int(size == 3 and i == 2)))
            for i, t in enumerate(a)]


def diagonal(matrix):
    return (len(matrix) == 2
            and all(type(t) is list and t[:2] == [1, 1]
                    for t in matrix))


def derive(proof, context, scope):
    if type(proof) is not list or not proof or type(proof[0]) is not str:
        fail()
    tag = proof[0]
    if tag == 'h' and len(proof) == 2:
        index = proof[1]
        if type(index) is not int or not 0 <= index < len(context):
            fail()
        return context[index]
    if tag == 'q' and len(proof) == 4:
        witness, major, minor = proof[1:]
        if not term(witness, scope):
            fail()
        closed = derive(major, context, scope)
        if len(closed) != 2 or closed[0] != 'q':
            fail()
        if derive(minor, context, scope) != opening(closed[1], 0):
            fail()
        return opening(closed[1], witness)
    if tag == 'r' and len(proof) == 2:
        a = proof[1]
        if not term(a, scope):
            fail()
        return [a, a]
    if tag == 'v' and len(proof) == 3:
        s, t = derive(proof[1], context, scope)
        b, r = derive(proof[2], context, scope)
        c, a, h = b
        if c != 0:
            if len(c) != 2:
                fail()
            a, t = [c[1], a, h], opening(h, t)
        if a != s:
            fail()
        return [r, t]
    if tag in ('e', 'i') and len(proof) == 4:
        goal, data, branch = proof[1:]
        if not formula(goal, scope):
            fail()
        fresh = -scope - 1
        if tag == 'e':
            paired = derive(data, context, scope)
            if len(paired) != 1:
                fail()
            body = opening(paired[0], fresh, 1)
            clause = ['q', body]
            target = goal
        else:
            if len(goal) != 1 or not term(data, scope):
                fail()
            body = opening(goal[0], data, 1)
            eta = fresh if diagonal(goal[0]) else 0
            clause = opening(body, eta)
            target = opening(body, [0, fresh])
        if derive(branch, context + [clause], scope + 1) != target:
            fail()
        return goal
    fail()


def verify(data):
    if type(data) is not dict or set(data) != {'goal', 'proof'}:
        fail()
    if not formula(data['goal'], 0):
        fail()
    if derive(data['proof'], [], 0) != data['goal']:
        fail()
    return True


if __name__ == '__main__':
    try:
        verify(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
