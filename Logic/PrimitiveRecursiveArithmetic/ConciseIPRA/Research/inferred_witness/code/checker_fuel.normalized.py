import json

def need(condition):
    if not condition:
        raise ValueError('invalid certificate')

def spend():
    global remaining
    remaining -= 1
    need(remaining >= 0)

def walk(a, f, d=0, form=None):
    spend()
    if type(a) is int:
        need(not form)
        return f(a, d)
    need(type(a) is list)
    size = len(a)
    need(form is None or (size in (2, 1 if form else 3) and (form or size == 3 or a[0] == 0)))
    a = [walk(b, f, d + (2 if size == 1 else int(size == 3 and i == 2)), size == 1) for i, b in enumerate(a)]
    if size == 3:
        c, b, h = a
        if c == 0:
            return b
        if type(c) is list and len(c) == 2:
            return sub(h, walk([c[1], b, h], lambda i, d: i))
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
        case ['e', q, r]:
            D, = prove(q, g)
            B = sub(D, b, 1)
            u, E = (sub(B, 0), sub(B, [0, 0]))
            t0 = E[1] if u == [0, 0] and E[0] == b else b
            B = walk(B, lambda i, d: t0 if i == b else i)
            A = prove(r, g + [(u, B)])
        case ['i', B0, t, r]:
            syntax(t, n)
            B = sub(B0, t, 1)
            u = sub(B, b if len(B0) == 2 and (not t) else 0)
            need(prove(r, g + [([], u)]) == sub(B, [0, b]))
            A = [B0]
        case _:
            need(False)
    syntax(A, n, True)
    return A

def check(data):
    global remaining
    need(set(data) == {'goal', 'proof', 'fuel'})
    remaining = data['fuel']
    need(type(remaining) is int and remaining >= 0)
    syntax(data['goal'], 1, True)
    need(prove(data['proof'], [([], [1, 1])]) == data['goal'])
if __name__ == '__main__':
    check(json.load(open(0)))
    print('ACCEPT')
