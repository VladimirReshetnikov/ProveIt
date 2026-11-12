import json

def fail():
    raise ValueError('invalid certificate')

def valid(a, scope, depth=0, formula=False):
    if type(a) is int:
        return not formula and -scope <= a <= depth
    return type(a) is list and len(a) in ((1, 2) if formula else (2, 3)) and (formula or len(a) == 3 or a[0] == 0) and all((valid(t, scope, depth + 2 * (len(a) == 1) + (len(a) == 3 and j == 2), len(a) == 1) for j, t in enumerate(a)))

def opening(a, value, index=1):
    if type(a) is int:
        return value if a == index else a - (index > 0 and a > index)
    size = len(a)
    return [opening(t, value, index + (index > 0) * (2 * (size == 1) + (size == 3 and j == 2))) for j, t in enumerate(a)]

def derive(proof, context):
    scope = len(context)
    tag, *args = proof
    if tag == 'u':
        index, premise = args
        if type(index) is not int or not 0 <= index < len(context):
            fail()
        base, body = context[index]
        if base and derive(premise, context) != base:
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
        if not valid(goal, scope, formula=True):
            fail()
        source, target = derive(major, context)
        if type(source) is not int or source != -scope or scope == 0 or (derive(minor, context) != opening(goal, target, source)):
            fail()
        return goal
    if tag == 'a':
        target, branch = args
        if not valid(target, scope):
            fail()
        fresh = -scope - 1
        result = derive(branch, context + [([], [fresh, target])])
        return opening(result, target, fresh)
    if tag in ('e', 'i'):
        goal, data, branch = args
        if not valid(goal, scope, formula=True):
            fail()
        fresh = -scope - 1
        if tag == 'e':
            paired = derive(data, context)
            if len(paired) != 1:
                fail()
            body = opening(paired[0], fresh, 2)
            clause = (opening(body, 0), body)
            target = goal
        else:
            if len(goal) != 1 or not valid(data, scope):
                fail()
            body = opening(goal[0], data, 2)
            eta = fresh if len(goal[0]) == 2 and data == 0 else 0
            clause = ([], opening(body, eta))
            target = opening(body, [0, fresh])
        if derive(branch, context + [clause]) != target:
            fail()
        return goal
    fail()

data = json.load(open(0))
if set(data) != {'goal', 'proof'} or not valid(data['goal'], 0, formula=True) or derive(data['proof'], []) != data['goal']:
    fail()
print('ACCEPT')
