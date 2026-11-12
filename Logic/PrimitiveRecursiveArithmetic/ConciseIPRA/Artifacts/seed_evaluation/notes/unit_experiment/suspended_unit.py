"""Suspended-unit scalar iPRA with reusable clauses; experimental checker.

Terms use 0, positive bound indices, negative rigid free levels, s, i, u.
The u constructor binds one state variable in its update body. Iterators
with zero counters contract to their seeds; successor counters factor
into suspended u terms. Update bodies are not evaluated by normalization.
Every public syntax object must be canonical. Normalization and opening
traverse all children before contracting.
"""
import json
import sys


def require(condition):
    if not condition:
        raise ValueError('Invalid certificate')


def walk(a, f, depth=0, sort=-1):
    if type(a) is int:
        require(sort != 1)
        return f(a, depth)
    require(type(a) is list and a)
    tag, *args = a
    require(sort < 0 or (tag in ('=', 'd')) == sort)
    binders = {'s': [0], 'i': [0, 0, 1], 'u': [0, 1], '=': [0, 0], 'd': [2]}[tag]
    require(len(args) == len(binders))
    a = [tag] + [walk(b, f, depth + k, tag == 'd')
                 for b, k in zip(args, binders)]
    if tag == 'i':
        if a[1] == 0:
            return a[2]
        if type(a[1]) is list and a[1][0] == 's':
            return ['u', walk(['i', a[1][1], *a[2:]], lambda i, d: i), a[3]]
    return a


def syntax(a, scope, depth=0, sort=0):
    def variable(i, d):
        require(-scope <= i <= d)
        return i
    require(walk(a, variable, depth, sort) == a)


def opening(a, value, depth=0):
    return walk(a, lambda i, d: value if i == d + 1 else i - (i > d + 1), depth)


def derive(proof, context, scope):
    match proof:
        case ['u', index, witness, premise]:
            require(type(index) is int and 0 <= index < len(context))
            syntax(witness, scope)
            antecedent, body = context[index]
            require(derive(premise, context, scope) == antecedent)
            return opening(body, witness)
        case ['r', a]:
            syntax(a, scope)
            return ['=', a, a]
        case ['x', major, minor]:
            match derive(major, context, scope), derive(minor, context, scope):
                case ['=', s, t], ['=', ['u', a, h], r]:
                    require(s == a)
                    return ['=', r, opening(h, t)]
        case [('e' | 'i') as tag, goal, data, branch]:
            syntax(goal, scope, sort=1)
            fresh = -scope - 1
            if tag == 'e':
                paired = derive(data, context, scope)
                require(paired[0] == 'd')
                body = opening(paired[1], fresh, 1)
                clause = (opening(body, 0), body)
                target = goal
            else:
                require(goal[0] == 'd')
                syntax(data, scope)
                body = opening(goal[1], data, 1)
                eta = fresh if goal[1][0] == '=' and data == 0 else 0
                clause = (['=', 0, 0], opening(body, eta))
                target = opening(body, ['s', fresh])
            require(derive(branch, context + [clause], scope + 1) == target)
            return goal
    raise ValueError('Invalid proof')


def verify(data):
    require(type(data) is dict and set(data) == {'goal', 'proof'})
    syntax(data['goal'], 0, sort=1)
    require(derive(data['proof'], [], 0) == data['goal'])
    return True


if __name__ == '__main__':
    try:
        verify(json.load(sys.stdin))
    except Exception:
        sys.exit(1)
    print('ACCEPT')
