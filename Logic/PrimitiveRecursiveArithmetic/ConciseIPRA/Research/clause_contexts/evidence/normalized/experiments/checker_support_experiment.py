import json
import sys

def require(condition):
    if not condition:
        raise ValueError('Invalid certificate')

def iterator(n, a, h):
    return a if n == 0 else [n, a, h]

def support(a, scope, depth=0):
    if type(a) is int:
        require(a >= -scope)
        return max(a - depth, 0)
    require(type(a) is list and len(a) in (1, 3) and (len(a) == 1 or a[0] != 0))
    return max((support(t, scope, depth + (len(a) == 3 and i == 2)) for i, t in enumerate(a)))

def rank(a, scope):
    require(type(a) is list and len(a) == 2)
    return (max((support(t, scope) for t in a)) + 1) // 2

def opening(a, value, depth=0):
    if type(a) is int:
        return value if a == depth + 1 else a - (a > depth + 1)
    b = [opening(t, value, depth + (len(a) == 3 and i == 2)) for i, t in enumerate(a)]
    return iterator(*b) if len(a) == 3 else b

def instance(body, value, scope):
    k, s, t = body
    result = [opening(s, value, 2 * k), opening(t, value, 2 * k)]
    return result if rank(result, scope) == k else [0, 0]

def derive(proof, context, scope):
    match proof:
        case ['u', index, witness, [*premises]]:
            require(type(index) is int and 0 <= index < len(context) and (support(witness, scope) == 0))
            antecedent, body = context[index]
            require([derive(p, context, scope) for p in premises] == antecedent)
            return instance(body, witness, scope)
        case ['x', major, minor]:
            first, second = (derive(major, context, scope), derive(minor, context, scope))
            require(rank(first, scope) == rank(second, scope) == 0)
            match (first, second):
                case [[s, t], [[[n], a, h], r]]:
                    require(s == iterator(n, a, h))
                    return [r, opening(h, t)]
        case ['e' | 'i' as tag, goal, data, branch]:
            rank(goal, scope)
            fresh = -scope - 1
            source = derive(data, context, scope) if tag == 'e' else goal
            k = rank(source, scope)
            require(k > 0)
            witness = fresh if tag == 'e' else data
            body = [k - 1] + [opening(t, witness, 2 * k - 1) for t in source]
            if tag == 'e':
                clause = ([instance(body, 0, scope + 1)], body)
                target = goal
            else:
                require(support(data, scope) == 0)
                eta = fresh if k == 1 and data == 0 else 0
                fact = instance(body, eta, scope + 1)
                clause = ([], [rank(fact, scope + 1)] + fact)
                target = instance(body, [fresh], scope + 1)
            require(derive(branch, context + [clause], scope + 1) == target)
            return goal
    raise ValueError('Invalid proof')

def verify(data):
    require(type(data) is dict and set(data) == {'goal', 'proof'})
    rank(data['goal'], 0)
    require(derive(data['proof'], [([], [0, 1, 1])], 0) == data['goal'])
    return True
if __name__ == '__main__':
    try:
        verify(json.load(sys.stdin))
    except Exception:
        sys.exit(1)
    print('ACCEPT')
