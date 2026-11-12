"""Equality-aware witness elimination; full computation normal forms."""
import json
import sys


def require(condition):
    if not condition:
        raise ValueError('invalid certificate')


def walk(a, f, d=0, form=None):
    if type(a) is int:
        require(not form)
        return f(a, d)
    require(type(a) is list)
    size = len(a)
    require(size in (1, 2, 3) and (form is None or size in ((1, 2) if form else (2, 3)))
            and (form is not False or size == 3 or a[0] == 0))
    a = [walk(b, f, d + (2 if size == 1 else int(size == 3 and i == 2)), size == 1)
         for i, b in enumerate(a)]
    if size == 3:
        c, b, h = a
        if c == 0:
            return b
        if type(c) is list and len(c) == 2:
            return sub(h, walk([c[1], b, h], lambda i, d: i))
    return a


def syntax(a, n, form=False):
    def variable(i, d):
        require(-n <= i <= d)
        return i
    require(walk(a, variable, form=form) == a)


def shift(a, k):
    return walk(a, lambda i, d: i + k if i > d else i)


def sub(a, t, depth=0):
    return walk(a, lambda i, d: shift(t, d) if i == d + 1 else i - (i > d + 1), depth)


def derive(p, g, n):
    match p:
        case ['r', t]:
            syntax(t, n)
            return [t, t]
        case ['u', j, t, p]:
            require(type(j) is int and 0 <= j < len(g))
            syntax(t, n)
            a, b = g[j]
            require(derive(p, g, n) == a)
            return sub(b, t)
        case ['e', goal, major, equality, branch]:
            syntax(goal, n, True)
            paired = derive(major, g, n)
            require(len(paired) == 1)
            b = sub(paired[0], -n - 1, 1)
            context = g + [(sub(b, 0), b)]
            equation = derive(equality, context, n + 1)
            require(len(equation) == 2 and equation[0] == -n - 1)
            require(walk(derive(branch, context, n + 1),
                         lambda i, d: equation[1] if i == -n - 1 else i) == goal)
            return goal
        case ['i', goal, t, branch]:
            syntax(goal, n, True)
            require(len(goal) == 1)
            syntax(t, n)
            b = sub(goal[0], t, 1)
            h = sub(b, -n - 1 if len(b) == 2 and t == 0 else 0)
            require(derive(branch, g + [([0, 0], h)], n + 1) == sub(b, [0, -n - 1]))
            return goal
    raise ValueError('invalid proof')


def check(data):
    require(type(data) is dict and set(data) == {'goal', 'proof'})
    syntax(data['goal'], 0, True)
    require(derive(data['proof'], [], 0) == data['goal'])


if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
