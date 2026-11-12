import json
import sys

def fail():
    raise ValueError('invalid certificate')

def rec(n, a, h):
    return [n, a, 0 if n == 0 else h]

def successor(a):
    return [0, a, 0]

def term(a, scope, depth=0):
    if type(a) is int:
        return -scope <= a <= depth
    return type(a) is list and len(a) == 3 and (a[0] != 0 or a[2] == 0) and all((term(t, scope, depth + 2 * (i == 2)) for i, t in enumerate(a)))

def formula(a, scope, depth=0):
    return type(a) is list and (len(a) == 2 and all((term(t, scope, depth) for t in a)) or (len(a) == 1 and formula(a[0], scope, depth + 2)))

def opening(a, value, depth=0):
    if type(a) is int:
        return value if a == depth + 1 else a - (a > depth + 1)
    size = len(a)
    result = [opening(t, value, depth + 2 * (size != 2 and i == size - 1)) for i, t in enumerate(a)]
    return rec(*result) if size == 3 else result

def derive(proof, context, scope):
    if type(proof) is not list or not proof or type(proof[0]) is not str:
        fail()
    tag = proof[0]
    if tag == 'u' and len(proof) == 4:
        index, witness, premise = proof[1:]
        if type(index) is not int or not 0 <= index < len(context) or (not term(witness, scope)):
            fail()
        antecedent, body = context[index]
        if derive(premise, context, scope) != antecedent:
            fail()
        return opening(body, witness)
    if tag == 'r' and len(proof) == 2:
        a = proof[1]
        if not term(a, scope):
            fail()
        return [a, a]
    if tag == 'v' and len(proof) == 3:
        s, t = derive(proof[1], context, scope)
        b, r = derive(proof[2], context, scope)
        c, a, h = b
        if c != successor(s):
            fail()
        return [r, opening(opening(h, rec(t, a, h)), t)]
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
            clause = (opening(body, 0), body)
            target = goal
        else:
            if len(goal) != 1 or not term(data, scope):
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
