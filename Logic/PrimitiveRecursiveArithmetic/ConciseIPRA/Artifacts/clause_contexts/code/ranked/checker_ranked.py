"""Four-rule clausal iPRA with ranked equations.

A formula [k, s, t] denotes k nested paired binders above the equation s=t.
Its terms are checked at depth 2*k. All clause bodies have one additional
external binder; zero-counter iterators contract during term opening.
"""
import json
import sys


def require(condition):
    if not condition:
        raise ValueError('Invalid certificate')


def iterator(n, a, h):
    return a if n == 0 else ['i', n, a, h]


def term(a, scope, depth=0):
    if type(a) is int:
        return -scope <= a <= depth
    if type(a) is not list:
        return False
    if len(a) == 2 and a[0] == 's':
        return term(a[1], scope, depth)
    return (len(a) == 4 and a[0] == 'i' and a[1] != 0
            and term(a[1], scope, depth) and term(a[2], scope, depth)
            and term(a[3], scope, depth + 1))


def formula(a, scope):
    return (type(a) is list and len(a) == 3
            and type(a[0]) is int and a[0] >= 0
            and all(term(t, scope, 2 * a[0]) for t in a[1:]))


def opening(a, value, depth=0):
    if type(a) is int:
        return value if a == depth + 1 else a - (a > depth + 1)
    tag = a[0]
    b = [opening(t, value, depth + int(tag == 'i' and i == 2))
         for i, t in enumerate(a[1:])]
    return iterator(*b) if tag == 'i' else [tag] + b


def instance(a, value, depth=0):
    k, s, t = a
    return [k, opening(s, value, 2 * k + depth),
            opening(t, value, 2 * k + depth)]


def derive(proof, context, scope):
    match proof:
        case ['u', index, witness, [*premises]]:
            require(type(index) is int and 0 <= index < len(context)
                    and term(witness, scope))
            antecedent, body = context[index]
            require([derive(p, context, scope) for p in premises] == antecedent)
            return instance(body, witness)
        case ['x', major, minor]:
            match derive(major, context, scope), derive(minor, context, scope):
                case [0, s, t], [0, ['i', ['s', n], a, h], r]:
                    require(s == iterator(n, a, h))
                    return [0, r, opening(h, t)]
        case [('e' | 'i') as tag, goal, data, branch]:
            require(formula(goal, scope))
            fresh = -scope - 1
            if tag == 'e':
                k, s, t = derive(data, context, scope)
                require(k > 0)
                body = instance([k - 1, s, t], fresh, 1)
                clause = ([instance(body, 0)], body)
                target = goal
            else:
                k, s, t = goal
                require(k > 0 and term(data, scope))
                body = instance([k - 1, s, t], data, 1)
                eta = fresh if k == 1 and data == 0 else 0
                clause = ([], instance(body, eta))
                target = instance(body, ['s', fresh])
            require(derive(branch, context + [clause], scope + 1) == target)
            return goal
    raise ValueError('Invalid proof')


def verify(data):
    require(type(data) is dict and set(data) == {'goal', 'proof'})
    require(formula(data['goal'], 0))
    require(derive(data['proof'], [([], [0, 1, 1])], 0) == data['goal'])
    return True


if __name__ == '__main__':
    try:
        verify(json.load(sys.stdin))
    except Exception:
        sys.exit(1)
    print('ACCEPT')
