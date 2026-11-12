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
    need(form is None or (size in ((1, 2) if form else (2, 3)) and (form or size == 3 or a[0] == 0)))
    a = [walk(b, f, d + (2 if size == 1 else int(size == 3 and i == 2)), size == 1) for i, b in enumerate(a)]
    if size == 3:
        c, b, h = a
        if c == 0:
            return b
        if type(c) is list and len(c) == 2:
            return sub(h, walk([c[1], b, h], lambda i, d: i))
    return a

def syntax(a, n, form=False, depth=0):

    def variable(i, d):
        need(-n <= i <= d)
        return i
    need(walk(a, variable, depth, form=form) == a)

def shift(a, k):
    return walk(a, lambda i, d: i + k if i > d else i)

def sub(a, t, depth=0):
    return walk(a, lambda i, d: shift(t, d) if i == d + 1 else i - (i > d + 1), depth)

def prove(a, p, g, n):
    syntax(a, n, True)
    match p:
        case ['u', j, t, premise]:
            need(type(j) is int and 0 <= j < len(g))
            syntax(t, n)
            base, body = g[j]
            need(a == sub(body, t))
            if base:
                prove(base, premise, g, n)
        case ['e', body, major, branch]:
            prove([body], major, g, n)
            body = sub(body, -n - 1, 1)
            prove(a, branch, g + [(sub(body, 0), body)], n + 1)
        case ['t', h, s, t, major, minor]:
            need(len(a) == 2)
            syntax(h, n, False, 1)
            prove([s, t], major, g, n)
            prove([sub(h, s), a[0]], minor, g, n)
            need(a[1] == sub(h, t))
        case ['i', t, branch]:
            need(len(a) == 1)
            syntax(t, n)
            body = sub(a[0], t, 1)
            hyp = sub(body, -n - 1 if len(body) == 2 and t == 0 else 0)
            prove(sub(body, [0, -n - 1]), branch, g + [([], hyp)], n + 1)
        case _:
            raise ValueError('invalid proof')

def check(data):
    need(type(data) is dict and set(data) == {'goal', 'proof'})
    prove(data['goal'], data['proof'], [([], [1, 1])], 0)
if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
