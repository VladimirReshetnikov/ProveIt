"""Five-rule clausal iPRA with zero-normal iterators and uniform successor Step.

Numerical syntax: 0; integer bound indices (>0) or free levels (<0);
['s', term]; ['i', counter, seed, body]. Only body binds one variable.
Formula syntax: ['=', left, right]; ['d', matrix]. D binds x then y,
so the matrix uses index 1 for y and 2 for x. Zero-counter iterators
are excluded, and opening contracts them when substitution exposes one.
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


def formula(a, scope, depth=0):
    return (type(a) is list
            and (len(a) == 3 and a[0] == '='
                 and all(term(t, scope, depth) for t in a[1:])
                 or len(a) == 2 and a[0] == 'd'
                 and formula(a[1], scope, depth + 2)))


def opening(a, value, depth=0):
    if type(a) is int:
        return value if a == depth + 1 else a - (a > depth + 1)
    tag = a[0]
    b = [opening(t, value, depth + (2 if tag == 'd' else int(tag == 'i' and i == 2)))
         for i, t in enumerate(a[1:])]
    return iterator(*b) if tag == 'i' else [tag] + b


def derive(proof, context, scope):
    match proof:
        case ['u', index, premise]:
            require(type(index) is int and 0 <= index < len(context)
                   )
            antecedent, body = context[index]
            require(derive(premise, context, scope) == antecedent)
            return opening(body, -scope if index else ['s', 0])
        case ['r', a]:
            require(term(a, scope))
            return ['=', a, a]
        case ['x', major, minor]:
            match derive(major, context, scope), derive(minor, context, scope):
                case ['=', s, t], ['=', ['i', ['s', n], a, h], r]:
                    require(s == iterator(n, a, h))
                    return ['=', r, opening(h, t)]
        case [('e' | 'i') as tag, goal, data, branch]:
            require(formula(goal, scope))
            fresh = -scope - 1
            if tag == 'e':
                paired = derive(data, context, scope)
                require(paired[0] == 'd')
                body = opening(paired[1], fresh, 1)
                clause = (opening(body, 0), body)
                target = goal
            else:
                require(goal[0] == 'd' and term(data, scope))
                body = opening(goal[1], data, 1)
                eta = fresh if goal[1][0] == '=' and data == 0 else 0
                clause = (['=', 0, 0], opening(body, eta))
                target = opening(body, ['s', fresh])
            require(derive(branch, [clause] + context, scope + 1) == target)
            return goal
    raise ValueError('Invalid proof')


def verify(data):
    require(type(data) is dict and set(data) == {'goal', 'proof'})
    require(formula(data['goal'], 0))
    require(derive(data['proof'], [], 0) == data['goal'])
    return True


if __name__ == '__main__':
    try:
        verify(json.load(sys.stdin))
    except Exception:
        sys.exit(1)
    print('ACCEPT')
