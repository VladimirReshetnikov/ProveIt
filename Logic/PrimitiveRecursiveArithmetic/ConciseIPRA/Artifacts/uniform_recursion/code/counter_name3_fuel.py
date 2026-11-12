import json

def need(condition):
    if not condition:
        raise ValueError('invalid certificate')

fuel = 0

def spend():
    global fuel
    need(fuel > 0)
    fuel -= 1

def walk(a, f, d=0, form=None):
    spend()
    if type(a) is int:
        need(not form)
        return f(a, d)
    need(type(a) is list)
    size = len(a)
    need(form is None or size in ((1, 2) if form else (3,)))
    a = [walk(b, f, d + 2 * (size == 1 or i == 2), size == 1) for i, b in enumerate(a)]
    if size == 3:
        c, b, h = a
        if c == 0:
            return [0, b, 0]
        if type(c) is list and c[0] == 0:
            return sub(sub(h, c[1], 1), walk([c[1], b, h], lambda i, d: i))
    return a

def syntax(a, n, form=False):
    need(walk(a, lambda i, d: need(1 - n <= i <= d) or i, form=form) == a)

def sub(a, t, depth=0):
    return walk(a, lambda i, d: walk(t, lambda j, e: j + d if j > e else j) if i == d + 1 else i - (i > d + 1), depth)

def prove(p, g):
    spend()
    n = len(g)
    b = -n
    match p:
        case ['u', j, t, q]:
            need(type(j) is int and 0 <= j < n)
            syntax(t, n)
            u, B = g[j]
            if u:
                need(prove(q, g) == u)
            A = sub(B, t)
        case ['e', q, e, r]:
            D, = prove(q, g)
            B = sub(D, b, 1)
            local = g + [(sub(B, 0), B)]
            x, t0 = prove(e, local)
            need(x == b)
            A = prove(r, local)
            A = walk(A, lambda i, d: t0 if i == b else i)
        case ['i', B0, t, r]:
            syntax(t, n)
            B = sub(B0, t, 1)
            u = sub(B, b if len(B0) == 2 and (not t) else 0)
            need(prove(r, g + [([], u)]) == sub(B, [0, b, 0]))
            A = [B0]
        case _:
            need(False)
    syntax(A, n, True)
    return A

def check(data):
    global fuel
    need(set(data) == {'goal', 'proof', 'fuel'})
    fuel = data['fuel']
    need(type(fuel) is int and fuel >= 0)
    syntax(data['goal'], 1, True)
    need(prove(data['proof'], [([], [1, 1])]) == data['goal'])
if __name__ == '__main__':
    check(json.load(open(0)))
    print('ACCEPT')
