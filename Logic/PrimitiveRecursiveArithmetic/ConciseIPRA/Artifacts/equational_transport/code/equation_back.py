"""The new A_nu^= checker. Backward substitution concludes an equation.
All other rules and input validation match the pinned newest-parameter checker.
"""
import json
import sys


def fail():
    raise ValueError('invalid certificate')


def valid(a, scope, depth=0, formula=False):
    if type(a) is int:
        return not formula and -scope <= a <= depth
    return (type(a) is list
            and len(a) in ((1, 2) if formula else (2, 3))
            and (formula or len(a) == 3 or a[0] == 0)
            and all(valid(t, scope,
                          depth + 2 * (len(a) == 1) + (len(a) == 3 and j == 2),
                          len(a) == 1)
                    for j, t in enumerate(a)))


def opening(a, value, index=1):
    if type(a) is int:
        return value if a == index else a - (index > 0 and a > index)
    size = len(a)
    return [opening(t, value,
                    index + (index > 0) * (2 * (size == 1) + (size == 3 and j == 2)))
            for j, t in enumerate(a)]


def derive(proof, context, scope):
    tag, *args = proof
    if tag == 'u':
        index, premise = args
        if type(index) is not int or not 0 <= index < len(context):
            fail()
        base, body = context[index]
        if base and derive(premise, context, scope) != base:
            fail()
        return opening(body, -scope)
    if tag == 'c':
        counter, seed, body = args
        term = [counter, seed, body]
        if not valid(term, scope):
            fail()
        if counter == 0:
            return [term, seed]
        _, counter = counter
        return [term, opening(body, [counter, seed, body])]
    if tag == 'v':
        goal, major, minor = args
        if not valid(goal, scope, formula=True) or len(goal) != 2:
            fail()
        source, target = derive(major, context, scope)
        if (type(source) is not int or source != -scope or scope == 0
                or derive(minor, context, scope) != opening(goal, target, source)):
            fail()
        return goal
    if tag == 'a':
        target, branch = args
        if not valid(target, scope):
            fail()
        fresh = -scope - 1
        result = derive(branch, context + [([], [fresh, target])], scope + 1)
        return opening(result, target, fresh)
    if tag in ('e', 'i'):
        goal, *args = args
        if not valid(goal, scope, formula=True):
            fail()
        fresh = -scope - 1
        if tag == 'e':
            data, branch = args
            paired = derive(data, context, scope)
            if len(paired) != 1:
                fail()
            body = opening(paired[0], fresh, 2)
            clause = (opening(body, 0), body)
            target = goal
        else:
            branch, = args
            if len(goal) != 1:
                fail()
            body = opening(goal[0], -scope, 2)
            eta = fresh if len(goal[0]) == 2 and all(
                type(t) is list and len(t) == 3 and t[:2] == [1, 1]
                for t in goal[0]) else 0
            clause = ([], opening(body, eta))
            target = opening(body, [0, fresh])
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
