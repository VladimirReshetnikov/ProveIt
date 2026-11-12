"""Strict raw clausal iPRA checker with two-case computational equality.

Terms are ['z'], ['v', i], ['s', t], and ['i', n, a, h].
Formulas are ['=', s, t] and ['d', B]. Positive variables are bound
indices; negative variables are fresh free levels. Input is {'goal': F,
'proof': P}. Clause contexts are maintained by the checker.
"""
import json
import sys


def require(condition):
    if not condition:
        raise ValueError('invalid certificate')


def walk(a, variable, depth=0, sort=-1):
    require(type(a) is list and a)
    tag, *args = a
    require(sort < 0 or (tag in ('=', 'd')) == sort)
    if tag == 'v':
        require(len(args) == 1)
        return variable(args[0], depth)
    binders = {'z': [], 's': [0], 'i': [0, 0, 1], '=': [0, 0], 'd': [2]}[tag]
    require(len(args) == len(binders))
    return [tag] + [walk(t, variable, depth + k, tag == 'd')
                    for t, k in zip(args, binders)]


def syntax(a, scope, sort=0):
    def variable(i, depth):
        require(type(i) is int and i != 0 and -scope <= i <= depth)
        return ['v', i]
    walk(a, variable, sort=sort)


def opening(a, value, depth=0):
    return walk(a, lambda i, d: value if i == d + 1 else ['v', i - (i > d + 1)], depth)


def derive(proof, context, scope):
    match proof:
        case ['r', a]:
            syntax(a, scope)
            return ['=', a, a]
        case ['u', j, t, p]:
            require(type(j) is int and 0 <= j < len(context))
            syntax(t, scope)
            base, body = context[j]
            require(derive(p, context, scope) == base)
            return opening(body, t)
        case ['v', p, q]:
            _, s, t = derive(p, context, scope)
            _, (_, counter, seed, body), r = derive(q, context, scope)
            if counter == ['z']:
                require(seed == s)
            else:
                require(counter[0] == 's' and s == ['i', counter[1], seed, body])
                t = opening(body, t)
            return ['=', r, t]
        case ['e', p, q]:
            paired = derive(p, context, scope)
            require(paired[0] == 'd')
            body = opening(paired[1], ['v', -scope - 1], 1)
            clause = (opening(body, ['z']), body)
            a = derive(q, context + [clause], scope + 1)
            syntax(a, scope, 1)
            return a
        case ['i', b, t, p]:
            syntax(['d', b], scope, 1)
            syntax(t, scope)
            fresh = ['v', -scope - 1]
            body = opening(b, t, 1)
            eta = fresh if b[0] == '=' and t == ['z'] else ['z']
            clause = (['=', ['z'], ['z']], opening(body, eta))
            require(derive(p, context + [clause], scope + 1) == opening(body, ['s', fresh]))
            return ['d', b]
        case _:
            raise ValueError('invalid proof')


def verify(data):
    require(type(data) is dict and set(data) == {'goal', 'proof'})
    syntax(data['goal'], 0, 1)
    require(derive(data['proof'], [], 0) == data['goal'])


if __name__ == '__main__':
    try:
        verify(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
