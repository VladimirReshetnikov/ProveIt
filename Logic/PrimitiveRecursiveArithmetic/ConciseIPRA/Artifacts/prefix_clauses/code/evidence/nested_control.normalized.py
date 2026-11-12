import json
import sys

def require(condition):
    if not condition:
        raise ValueError('invalid certificate')

def term(a, scope, depth=0):
    if type(a) is int:
        return -scope <= a <= depth
    return type(a) is list and len(a) in (1, 3) and all((term(t, scope, depth + (len(a) == 3 and i == 2)) for i, t in enumerate(a)))

def formula(a, scope, depth=0):
    return type(a) is list and (len(a) == 2 and all((term(t, scope, depth) for t in a)) or (len(a) == 1 and formula(a[0], scope, depth + 2)))

def sub(a, value, index=1):
    if type(a) is int:
        return value if a == index else a - (a > index)
    return [sub(t, value, index + (len(a) == 3 and i == 2)) for i, t in enumerate(a)]

def opening(a, value, offset=0):
    if len(a) == 1:
        return [opening(a[0], value, offset + 2)]
    return [sub(t, value, 1 + offset) for t in a]

def reflexive(a):
    return reflexive(a[0]) if len(a) == 1 else a[0] == a[1]

def derive(proof, context):
    scope = len(context) - 1
    match proof:
        case ['u', index, witness, premise]:
            require(type(index) is int and 0 <= index < len(context) and term(witness, scope))
            base, body = context[index]
            require(reflexive(base) or derive(premise, context) == base)
            return opening(body, witness)
        case ['v', major, minor]:
            s, t = derive(major, context)
            b, r = derive(minor, context)
            c, a, h = b
            if c != 0:
                require(type(c) is list and len(c) == 1)
                a, t = ([c[0], a, h], sub(h, t))
            require(a == s)
            return [r, t]
        case ['e', major, branch]:
            paired = derive(major, context)
            require(len(paired) == 1)
            body = opening(paired[0], -scope - 1, 1)
            result = derive(branch, context + [(opening(body, 0), body)])
            require(formula(result, scope))
            return result
        case ['i', goal, witness, branch]:
            require(formula(goal, scope) and len(goal) == 1 and term(witness, scope))
            body = opening(goal[0], witness, 1)
            fresh = -scope - 1
            eta = fresh if len(goal[0]) == 2 and witness == 0 else 0
            require(derive(branch, context + [([0, 0], opening(body, eta))]) == opening(body, [fresh]))
            return goal
        case _:
            raise ValueError('invalid proof')

def verify(data):
    require(type(data) is dict and set(data) == {'goal', 'proof'} and formula(data['goal'], 0))
    require(derive(data['proof'], [([0, 0], [1, 1])]) == data['goal'])
if __name__ == '__main__':
    try:
        verify(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
