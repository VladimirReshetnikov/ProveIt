"""Canonical successor-seeded iPRA with substitutive witness discharge.

Terms: integer 0; negative free levels; positive bound indices; [n,a,h].
R(0,a;u.h) is canonically [0,a,0], and S(a) abbreviates [0,a,0].
Formulas: [s,t] or [B], with D binding x at index 2 and y at index 1.
Four instructions: c (successor calculation), u (clause use),
i (paired introduction), e (substitutive witness discharge).
No reflexivity axiom and no execution of iterator bodies by normalization.
Input: exactly {'goal': closed_formula, 'proof': finite_proof_tree}.
"""
import json
import sys


def need(condition):
    if not condition:
        raise ValueError('invalid certificate')


def walk(a, f, d=0, form=None):
    if type(a) is int:
        need(not form)
        return f(a, d)
    need(type(a) is list)
    size = len(a)
    need(form is None or size in ((1, 2) if form else (3,)))
    a = [walk(b, f, d + (2 if size == 1 else int(size == 3 and i == 2)), size == 1)
         for i, b in enumerate(a)]
    if size == 3 and a[0] == 0:
        a[2] = 0
    return a


def syntax(a, n, form=False, depth=0):
    def variable(i, d):
        need(-n <= i <= d)
        return i
    need(walk(a, variable, depth, form) == a)


def sub(a, t, depth=0):
    return walk(a, lambda i, d: t if i == d + 1 else i - (i > d + 1), depth)


H = [0, 0]


def prove(a, p, g, n):
    syntax(a, n, True)
    match p:
        case ['c']:
            need(len(a) == 2)
            counter, seed, body = a[0]
            need(type(counter) is list and counter[0] == 0)
            prev = [counter[1], seed, body if counter[1] else 0]
            need(a[1] == sub(body, prev))
        case ['u', j, t, premise]:
            need(type(j) is int and 0 <= j < len(g))
            syntax(t, n)
            base, body = g[j]
            need(a == sub(body, t))
            prove(base, premise, g, n)
        case ['i', t, branch]:
            need(len(a) == 1)
            syntax(t, n)
            body = sub(a[0], t, 1)
            hyp = sub(body, -n - 1 if len(body) == 2 and t == 0 else 0)
            prove(sub(body, [0, -n - 1, 0]), branch, g + [(H, hyp)], n + 1)
        case ['e', body, fml, s, t, major, eq, branch]:
            prove([body], major, g, n)
            body = sub(body, -n - 1, 1)
            local = g + [(sub(body, 0), body)]
            syntax(fml, n + 1, True, 1)
            prove([s, t], eq, local, n + 1)
            prove(sub(fml, s), branch, local, n + 1)
            need(a == sub(fml, t))
        case _:
            raise ValueError('invalid proof')


def check(data):
    need(type(data) is dict and set(data) == {'goal', 'proof'})
    prove(data['goal'], data['proof'], [], 0)


if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
