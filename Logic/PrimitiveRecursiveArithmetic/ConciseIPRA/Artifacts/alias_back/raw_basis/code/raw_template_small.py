import json

def fail():
    raise ValueError('invalid certificate')

def successor(a):
    return [0, a]

def valid(a, scope, depth=0, formula=False):
    if type(a) is int:
        return not formula and -scope <= a <= depth
    return type(a) is list and len(a) in ((1, 2) if formula else (2, 3)) and (formula or len(a) == 3 or a[0] == 0) and all((valid(t, scope, depth + 2 * (len(a) == 1) + (len(a) == 3 and i == 2), len(a) == 1) for i, t in enumerate(a)))

def opening(a, value, index=1):
    if type(a) is int:
        return value if a == index else a - (a > index)
    size = len(a)
    return [opening(t, value, index + 2 * (size == 1) + (size == 3 and i == 2)) for i, t in enumerate(a)]

def derive(proof, context):
    scope = len(context)
    tag, *args = proof
    if tag == 'u':
        index, witness, premise = args
        if type(index) is not int or not 0 <= index < len(context) or (not valid(witness, scope)):
            fail()
        antecedent, body = context[index]
        if antecedent and derive(premise, context) != antecedent:
            fail()
        return opening(body, witness)
    if tag == 'c':
        counter, seed, body = args
        term = [counter, seed, body]
        if not valid(term, scope):
            fail()
        if counter == 0:
            return [term, seed]
        _, counter = counter
        return [term, opening(body, [counter, seed, body])]
    if tag == 'x':
        template, major, minor = args
        if not valid(template, scope, 1):
            fail()
        s, t = derive(major, context)
        u, r = derive(minor, context)
        if u != opening(template, s):
            fail()
        return [r, opening(template, t)]
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
            target = opening(body, successor(fresh))
        if derive(branch, context + [clause]) != target:
            fail()
        return goal
    fail()

data = json.load(open(0))
if set(data) != {'goal', 'proof'} or not valid(data['goal'], 0, formula=True) or derive(data['proof'], []) != data['goal']:
    fail()
print('ACCEPT')
