"""Raw clausal control with three-case Eval.

The clause protocol, witness guard, validators, and goal-oriented interface
match the primary checker; zero iteration is not normalized.
"""
import json
import sys


def require(condition):
    if not condition:
        raise ValueError('invalid certificate')


def term(a, scope, depth=0):
    if type(a) is int:
        return -scope <= a <= depth
    return (type(a) is list and len(a) in (2, 3)
            and (len(a) == 3 or a[0] == 0)
            and all(term(t, scope, depth + (len(a) == 3 and i == 2))
                    for i, t in enumerate(a)))


def formula(a, scope, depth=0):
    return (type(a) is list
            and ((len(a) == 2 and all(term(t, scope, depth) for t in a))
                 or (len(a) == 1 and formula(a[0], scope, depth + 2))))


def opening(a, value, depth=0):
    if type(a) is int:
        return value if a == depth + 1 else a - (a > depth + 1)
    size = len(a)
    result = [opening(t, value, depth + (2 if size == 1 else int(size == 3 and i == 2)))
              for i, t in enumerate(a)]
    return result


def prove(a, p, g, n):
    require(formula(a, n))
    if len(a) == 2 and a[0] == a[1]:
        return
    match p:
        case ['v', b, s, t, major, minor]:
            prove([s, t], major, g, n)
            prove([b, a[0]], minor, g, n)
            if b != s:
                c, initializer, h = b
                if c != 0:
                    require(len(c) == 2)
                    initializer, t = [c[1], initializer, h], opening(h, t)
                require(initializer == s)
            require(len(a) == 2 and a[1] == t)
        case ['u', index, t, premise]:
            require(type(index) is int and 0 <= index < len(g) and term(t, n))
            antecedent, body = g[index]
            require(a == opening(body, t))
            prove(antecedent, premise, g, n)
        case ['e', body, major, branch]:
            prove([body], major, g, n)
            body = opening(body, -n - 1, 1)
            prove(a, branch, g + [(opening(body, 0), body)], n + 1)
        case ['i', t, branch]:
            require(len(a) == 1 and term(t, n))
            body = opening(a[0], t, 1)
            hypothesis = opening(body, -n - 1 if len(a[0]) == 2 and t == 0 else 0)
            prove(opening(body, [0, -n - 1]), branch, g + [([0, 0], hypothesis)], n + 1)
        case _:
            raise ValueError('invalid proof')


def check(c):
    require(type(c) is dict and set(c) == {'goal', 'proof'})
    prove(c['goal'], c['proof'], [], 0)


if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
