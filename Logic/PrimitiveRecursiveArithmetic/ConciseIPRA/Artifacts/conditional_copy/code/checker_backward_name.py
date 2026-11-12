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
    a = [walk(b, f, d + 2 * (size != 2 and j == size - 1), size == 1) for j, b in enumerate(a)]
    if size == 3:
        c, b, h = a
        if c == 0:
            return [0, b, 0]
        if type(c) is list and c[0] == 0:
            return sub(sub(h, c[1], 1), walk([c[1], b, h], lambda i, d: i))
    return a

def syntax(a, fresh, form=False):
    need(walk(a, lambda i, d: need(fresh < i <= d) or i, form=form) == a)

def sub(a, t, depth=0):
    return walk(a, lambda i, d: walk(t, lambda j, e: j + d if j > e else j) if i == d + 1 else i - (i > d + 1), depth)

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
        case ['e', body, template, t, major, eq, branch]:
            prove([body], major, g)
            body = sub(body, fresh, 1)
            local = g + [(sub(body, 0), body)]
            prove([fresh, t], eq, local)
            prove(sub(template, fresh), branch, local)
            need(sub(template, t) == a)
        case ['i', branch]:
            need(len(a) == 1)
            body = sub(a[0], fresh + 1, 1)
            base = sub(body, 0)
            hyp = sub(body, fresh) if base == [0, 0] else base
            prove(sub(body, [0, fresh, 0]), branch, g + [([], hyp)])
        case _:
            need(False)
goal, proof = json.load(open(0))
prove(goal, proof, [([], [1, 1])])
print('ACCEPT')
