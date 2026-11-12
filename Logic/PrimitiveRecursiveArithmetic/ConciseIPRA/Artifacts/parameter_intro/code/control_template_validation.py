"""Experimental three-rule counter-recursive calculus.

Terms are computation normal forms for R(n,a;i,u.h), with R(0,a;h)=S(a)
and R(S(n),a;h)=h(n,R(n,a;h)). Successor is [0,a,0]. R and D bind two
variables in their final child. Integers are zero, positive bound indices,
and negative free parameters. Formulas are equations [s,t] or D matrices [B].

The fixed initial clause is universal reflexivity. Introduction has no
witness field: it uses the newest available parameter, or zero at the root.
It is progressive exactly when the normalized zero row is reflexive.
Elimination also performs arbitrary equality transport in a checked template.
This candidate is supplied for mathematical review, not a correctness claim.
"""
import json


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
    a = [walk(b, f, d + 2 * (size != 2 and j == size - 1), size == 1)
         for j, b in enumerate(a)]
    if size == 3:
        c, b, h = a
        if c == 0:
            return [0, b, 0]
        if type(c) is list and c[0] == 0:
            return sub(sub(h, c[1], 1), walk([c[1], b, h], lambda i, d: i))
    return a


def syntax(a, fresh, form=False, depth=0):
    need(walk(a, lambda i, d: need(fresh < i <= d) or i, depth, form) == a)


def sub(a, t, depth=0):
    return walk(a, lambda i, d:
                walk(t, lambda j, e: j + d if j > e else j)
                if i == d + 1 else i - (i > d + 1), depth)


def prove(a, p, g):
    fresh = -len(g)
    syntax(a, fresh, True)
    match p:
        case ['u', j, t, premise]:
            need(type(j) is int and 0 <= j < len(g))
            syntax(t, fresh)
            base, body = g[j]
            need(a == sub(body, t))
            if base:
                prove(base, premise, g)
        case ['e', body, template, s, t, major, eq, branch]:
            prove([body], major, g)
            body = sub(body, fresh, 1)
            local = g + [(sub(body, 0), body)]
            syntax(template, fresh - 1, True, 1)
            prove([s, t], eq, local)
            prove(sub(template, s), branch, local)
            need(sub(template, t) == a)
        case ['i', branch]:
            need(len(a) == 1)
            body = sub(a[0], fresh + 1, 1)
            base = sub(body, 0)
            hyp = sub(body, fresh) if len(base) == 2 and base[0] == base[1] else base
            prove(sub(body, [0, fresh, 0]), branch, g + [([], hyp)])
        case _:
            need(False)


goal, proof = json.load(open(0))
prove(goal, proof, [([], [1, 1])])
print('ACCEPT')
