import json
import sys


def require(condition):
    if not condition:
        raise ValueError('invalid certificate')


def term(a, scope, depth=0):
    if type(a) is int:
        return -scope <= a <= depth
    return (type(a) is list and len(a) in (1, 3)
            and all(term(t, scope, depth + (len(a) == 3 and i == 2))
                    for i, t in enumerate(a)))


def formula(a, scope):
    return (type(a) is list and len(a) == 3 and type(a[0]) is int
            and a[0] >= 0 and all(term(t, scope, 2 * a[0]) for t in a[1:]))


def sub(a, value, index=1, delta=-1):
    if type(a) is int:
        return value if a == index and delta < 0 else a + delta * (a > index)
    return [sub(t, value, index + (len(a) == 3 and i == 2), delta)
            for i, t in enumerate(a)]


def opening(a, value, offset=0):
    k, s, t = a
    return [k, sub(s, value, 2 * k + 1 + offset), sub(t, value, 2 * k + 1 + offset)]


def gate(a):
    k, s, t = a
    h = sub(t, 0, 0, 1)
    return [k, [0, s, h], [2 * k + 1, s, h]]


def derive(proof, context):
    scope = len(context) - 1
    match proof:
        case ['u', index, witness, premise]:
            require(type(index) is int and 0 <= index < len(context) and term(witness, scope))
            body = context[index]
            base = opening(body, 0)
            require(base[1] == base[2] or derive(premise, context) == base)
            return opening(body, witness)
        case ['v', major, minor]:
            k, s, t = derive(major, context)
            j, b, r = derive(minor, context)
            require(k == j == 0)
            c, a, h = b
            if c != 0:
                require(type(c) is list and len(c) == 1)
                a, t = [c[0], a, h], sub(h, t)
            require(a == s)
            return [0, r, t]
        case ['e', major, branch]:
            k, s, t = derive(major, context)
            require(k > 0)
            body = opening([k - 1, s, t], -scope - 1, 1)
            result = derive(branch, context + [body])
            require(formula(result, scope))
            return result
        case ['i', goal, witness, branch]:
            require(formula(goal, scope) and goal[0] > 0 and term(witness, scope))
            k, s, t = goal
            body = opening([k - 1, s, t], witness, 1)
            fresh = -scope - 1
            eta = fresh if k == 1 and witness == 0 else 0
            require(derive(branch, context + [gate(opening(body, eta))]) == opening(body, [fresh]))
            return goal
        case _:
            raise ValueError('invalid proof')


def verify(data):
    require(type(data) is dict and set(data) == {'goal', 'proof'} and formula(data['goal'], 0))
    require(derive(data['proof'], [[0, 1, 1]]) == data['goal'])


if __name__ == '__main__':
    try:
        verify(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
