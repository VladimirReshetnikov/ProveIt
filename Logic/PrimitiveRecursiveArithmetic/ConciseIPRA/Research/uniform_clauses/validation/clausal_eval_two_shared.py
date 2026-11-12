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


def syntax(a, scope, depth=0, form=False):
    if type(a) is int:
        return not form and -scope <= a <= depth
    if type(a) is not list:
        return False
    arity = len(a)
    return (arity in ((1, 2) if form else (2, 3))
            and (form or arity == 3 or a[0] == 0)
            and all(syntax(t, scope,
                           depth + (2 if arity == 1 else int(arity == 3 and i == 2)),
                           arity == 1) for i, t in enumerate(a)))


def opening(a, value, depth=0):
    if type(a) is int:
        return value if a == depth + 1 else a - (a > depth + 1)
    size = len(a)
    return [opening(t, value, depth + (2 if size == 1 else int(size == 3 and i == 2)))
            for i, t in enumerate(a)]


def derive(proof, context, scope):
    if type(proof) is not list or not proof or type(proof[0]) is not str:
        fail()
    tag = proof[0]
    if tag == 'u' and len(proof) == 4:
        index, witness, premise = proof[1:]
        if (type(index) is not int or not 0 <= index < len(context)
                or not syntax(witness, scope)):
            fail()
        antecedent, body = context[index]
        if derive(premise, context, scope) != antecedent:
            fail()
        return opening(body, witness)
    if tag == 'r' and len(proof) == 2:
        a = proof[1]
        if not syntax(a, scope):
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
        if not syntax(goal, scope, form=True):
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
            if len(goal) != 1 or not syntax(data, scope):
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
    if type(data) is not dict or set(data) != {'goal', 'proof'}:
        fail()
    if not syntax(data['goal'], 0, form=True):
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

