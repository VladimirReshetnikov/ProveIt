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
    need(form is None or (size in ((1, 2) if form else (2, 3)) and (form or size == 3 or a[0] == 0)))
    a = [walk(b, f, d + (2 if size == 1 else int(size == 3 and i == 2)), size == 1) for i, b in enumerate(a)]
    if size == 3:
        c, b, h = a
        if c == 0:
            return b
        if type(c) is list and len(c) == 2:
            return sub(h, walk([c[1], b, h], lambda i, d: i))
    return a

def syntax(a, fresh, form=False):

    def variable(i, d):
        need(fresh < i <= d)
        return i
    need(walk(a, variable, form=form) == a)

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
        case ['e', body, fml, t, major, eq, branch]:
            prove([body], major, g)
            body = sub(body, fresh, 1)
            local = g + [(sub(body, 0), body)]
            prove([fresh, t], eq, local)
            prove(fml, branch, local)
            need(walk(fml, lambda i, d: t if i == fresh else i) == a)
        case ['i', t, branch]:
            need(len(a) == 1)
            syntax(t, fresh)
            body = sub(a[0], t, 1)
            hyp = sub(body, fresh if len(body) == 2 and t == 0 else 0)
            prove(sub(body, [0, fresh]), branch, g + [([], hyp)])
        case _:
            raise ValueError('invalid proof')
goal, proof = json.load(open(0))
prove(goal, proof, [([], [1, 1])])
print('ACCEPT')
