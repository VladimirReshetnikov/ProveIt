"""Raw clausal iPRA with computational equality.

Terms: 0, negative free levels, positive bound indices, [0,t] (S),
[n,a,h] (I). Formulas: [s,t] (equality), [B] (D).
Contexts contain (antecedent, one-bound-variable body) clauses.
Input: {'goal': a closed formula, 'proof': a finite proof tree}.
"""
import json
import sys


def fail():
    raise ValueError('invalid certificate')


def successor(a):
    return [0, a]


def valid(a, scope, depth=0, formula=False):
    if type(a) is int:
        return not formula and -scope <= a <= depth
    return (type(a) is list
            and len(a) in ((1, 2) if formula else (2, 3))
            and (formula or len(a) == 3 or a[0] == 0)
            and all(valid(t, scope,
                          depth + 2 * (len(a) == 1) + (len(a) == 3 and i == 2),
                          len(a) == 1)
                    for i, t in enumerate(a)))


def opening(a, value, depth=0):
    if type(a) is int:
        return value if a == depth + 1 else a - (a > depth + 1)
    size = len(a)
    return [opening(t, value, depth + 2 * (size == 1) + (size == 3 and i == 2))
            for i, t in enumerate(a)]


def derive(proof, context, scope):
    tag, *args = proof
    if tag == 'u':
        index, witness, premise = args
        if (type(index) is not int or not 0 <= index < len(context)
                or not valid(witness, scope)):
            fail()
        antecedent, body = context[index]
        if derive(premise, context, scope) != antecedent:
            fail()
        return opening(body, witness)
    if tag == 'r':
        a, = args
        if not valid(a, scope):
            fail()
        return [a, a]
    if tag == 'v':
        major, minor = args
        s, t = derive(major, context, scope)
        b, r = derive(minor, context, scope)
        c, a, h = b
        if c != 0:
            _, c = c
            a, t = [c, a, h], opening(h, t)
        if a != s:
            fail()
        return [r, t]
    if tag in ('e', 'i'):
        goal, data, branch = args
        if not valid(goal, scope, formula=True):
            fail()
        fresh = -scope - 1
        if tag == 'e':
            paired = derive(data, context, scope)
            if len(paired) != 1:
                fail()
            body = opening(paired[0], fresh, 1)
            clause = (opening(body, 0), body)
            target = goal
        else:
            if len(goal) != 1 or not valid(data, scope):
                fail()
            body = opening(goal[0], data, 1)
            eta = fresh if len(goal[0]) == 2 and data == 0 else 0
            clause = ([0, 0], opening(body, eta))
            target = opening(body, successor(fresh))
        if derive(branch, context + [clause], scope + 1) != target:
            fail()
        return goal
    fail()


def verify(data):
    if set(data) != {'goal', 'proof'}:
        fail()
    if not valid(data['goal'], 0, formula=True):
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

