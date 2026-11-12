import json
import sys

def require(condition):
    if not condition:
        raise ValueError('Invalid certificate')

def iterator(n, a, h):
    return a if n == 0 else [n, a, h]

def term(a, scope, depth=0):
    if type(a) is int:
        return -scope <= a <= depth
    return type(a) is list and len(a) in (1, 3) and (len(a) == 1 or a[0] != 0) and all((term(t, scope, depth + (len(a) == 3 and i == 2)) for i, t in enumerate(a)))

def formula(a, scope, depth=0):
    return type(a) is list and len(a) == 2 and (formula(a[1], scope, depth + 2) if a[0] == 'd' else all((term(t, scope, depth) for t in a)))

def opening(a, value, depth=0):
    if type(a) is int:
        return value if a == depth + 1 else a - (a > depth + 1)
    if a[0] == 'd':
        return ['d', opening(a[1], value, depth + 2)]
    b = [opening(t, value, depth + (len(a) == 3 and i == 2)) for i, t in enumerate(a)]
    return iterator(*b) if len(a) == 3 else b

def derive(proof, context):
    scope = len(context) - 1
    match proof:
        case ['u', index, witness, [*premises]]:
            require(type(index) is int and 0 <= index < len(context) and term(witness, scope))
            antecedent, body = context[index]
            require([derive(p, context) for p in premises] == antecedent)
            return opening(body, witness)
        case ['x', major, minor]:
            match (derive(major, context), derive(minor, context)):
                case [[s, t], [[[n], a, h], r]]:
                    require(s == iterator(n, a, h))
                    return [r, opening(h, t)]
        case ['e' | 'i' as tag, goal, data, branch]:
            require(formula(goal, scope))
            fresh = -scope - 1
            source = derive(data, context) if tag == 'e' else goal
            require(source[0] == 'd')
            body = opening(source[1], fresh if tag == 'e' else data, 1)
            if tag == 'e':
                clause = ([opening(body, 0)], body)
                target = goal
            else:
                require(term(data, scope))
                eta = fresh if source[1][0] != 'd' and data == 0 else 0
                clause = ([], opening(body, eta))
                target = opening(body, [fresh])
            require(derive(branch, context + [clause]) == target)
            return goal
    raise ValueError('Invalid proof')

def verify(data):
    require(type(data) is dict and set(data) == {'goal', 'proof'})
    require(formula(data['goal'], 0))
    require(derive(data['proof'], [([], [1, 1])]) == data['goal'])
    return True
if __name__ == '__main__':
    try:
        verify(json.load(sys.stdin))
    except Exception:
        sys.exit(1)
    print('ACCEPT')
