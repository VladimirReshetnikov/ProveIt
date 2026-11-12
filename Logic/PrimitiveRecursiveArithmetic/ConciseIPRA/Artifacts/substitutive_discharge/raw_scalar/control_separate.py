"""Matched raw control with separate equality transport and D-elimination.

Identical syntax, validators, computation, clause contexts and introduction
as checker.py. Its five families are c, u, i, e, t. Only the fused e family
is split into ordinary D elimination and unrestricted formula transport.
"""
import json
import sys


def need(condition):
    if not condition:
        raise ValueError('invalid certificate')


def walk(a, f, depth=0, form=None):
    if type(a) is int:
        need(not form)
        return f(a, depth)
    need(type(a) is list)
    size = len(a)
    need(form is None or size in ((1, 2) if form else (2, 3))
         and (form or size == 3 or a[0] == 0))
    return [walk(b, f, depth + (2 if size == 1 else int(size == 3 and i == 2)), size == 1)
            for i, b in enumerate(a)]


def syntax(a, scope, depth=0, form=False):
    def variable(i, d):
        need(-scope <= i <= d)
        return i
    walk(a, variable, depth, form)


def opening(a, value, depth=0):
    # Every inserted value has no loose positive indices. Its free parameters
    # are negative levels, so entering a binder cannot capture them.
    return walk(a, lambda i, d: value if i == d + 1 else i - (i > d + 1), depth)


def derive(p, g, n):
    match p:
        case ['c', b]:
            syntax(b, n)
            c, a, h = b
            if c == 0:
                return [b, a]
            need(type(c) is list and len(c) == 2)
            return [b, opening(h, [c[1], a, h])]
        case ['u', j, t, premise]:
            need(type(j) is int and 0 <= j < len(g))
            syntax(t, n)
            base, body = g[j]
            need(derive(premise, g, n) == base)
            return opening(body, t)
        case ['i', goal, t, branch]:
            syntax(goal, n, form=True)
            need(len(goal) == 1)
            syntax(t, n)
            body = opening(goal[0], t, 1)
            start = -n - 1 if len(body) == 2 and t == 0 else 0
            hyp = opening(body, start)
            need(derive(branch, g + [([[0, 0, 0], 0], hyp)], n + 1)
                 == opening(body, [0, -n - 1]))
            return goal
        case ['e', goal, major, branch]:
            syntax(goal, n, form=True)
            paired = derive(major, g, n)
            need(len(paired) == 1)
            body = opening(paired[0], -n - 1, 1)
            local = g + [(opening(body, 0), body)]
            need(derive(branch, local, n + 1) == goal)
            return goal
        case ['t', template, equality, branch]:
            s, t = derive(equality, g, n)
            syntax(template, n, 1, True)
            need(derive(branch, g, n) == opening(template, s))
            return opening(template, t)
        case _:
            raise ValueError('invalid proof')


def check(data):
    need(type(data) is dict and set(data) == {'goal', 'proof'})
    syntax(data['goal'], 0, form=True)
    need(derive(data['proof'], [], 0) == data['goal'])


if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
