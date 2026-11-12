# Complete goal-directed computation-normal Eq/D clause checker.
# Public assumptions are formulas; retained implications are internal clauses.
import json
import sys


def require(condition):
    if not condition:
        raise ValueError('Invalid certificate')


def walk(a, f, d=0, sort=-1):
    require(type(a) is list and a)
    tag, *args = a
    require(sort < 0 or (tag in ('=', 'd')) == sort)
    if tag == 'v':
        require(len(args) == 1)
        return f(args[0], d)
    binders = {'z': [], 's': [0], 'i': [0, 0, 1], '=': [0, 0], 'd': [2]}[tag]
    require(len(args) == len(binders))
    a = [tag] + [walk(b, f, d + k, tag == 'd') for b, k in zip(args, binders)]
    return a[2] if a[:2] == ['i', ['z']] else sub(a[3], [tag, a[1][1], *a[2:]]) if tag == 'i' and a[1][0] == 's' else a


def syntax(a, n, sort=0):
    def variable(i, d):
        require(type(i) is int and 0 <= i < n + d)
        return ['v', i]
    require(walk(a, variable, sort=sort) == a)


def shift(a, k=1, cutoff=0):
    return walk(a, lambda i, d: ['v', i + k if i >= d else i], cutoff)


def sub(a, t, drop=1, index=0):
    return walk(a, lambda i, d: ['v', i] if i < d + index else shift(t, d) if i == d + index else ['v', i - drop])


def lift(g):
    return [(shift(a), shift(b, cutoff=1)) for a, b in g]


def derive(p, g, n):
    match p:
        case ['r', t]:
            syntax(t, n)
            return ['=', t, t]
        case ['u', j, t, p]:
            require(type(j) is int and 0 <= j < len(g))
            syntax(t, n)
            a, b = g[j]
            require(derive(p, g, n) == a)
            return sub(b, t)
        case ['x', h, p, q]:
            syntax(h, n + 1)
            equation = derive(p, g, n)
            instance = derive(q, g, n)
            require(equation[0] == instance[0] == '=' and instance[1] == sub(h, equation[1]))
            return ['=', instance[2], sub(h, equation[2])]
        case [('e' | 'i') as tag, goal, data, branch]:
            syntax(goal, n, 1)
            if tag == 'e':
                major = derive(data, g, n)
                require(major[0] == 'd')
                b = major[1]
                clause = (sub(b, ['z']), b)
                target = shift(goal)
            else:
                require(goal[0] == 'd')
                syntax(data, n)
                b = sub(goal[1], shift(data), index=1)
                h = b if b[0] == '=' and data == ['z'] else shift(sub(b, ['z']))
                clause = (['=', ['z'], ['z']], shift(h))
                target = sub(b, ['s', ['v', 0]], 0)
            require(derive(branch, [clause] + lift(g), n + 1) == target)
            return goal
    raise ValueError('Invalid proof')


def verify(data):
    require(type(data) is dict and set(data) == {'goal', 'proof'})
    syntax(data['goal'], 0, 1)
    require(derive(data['proof'], [], 0) == data['goal'])
    return True


if __name__ == '__main__':
    try:
        verify(json.load(sys.stdin))
    except Exception:
        sys.exit(1)
    print('ACCEPT')
