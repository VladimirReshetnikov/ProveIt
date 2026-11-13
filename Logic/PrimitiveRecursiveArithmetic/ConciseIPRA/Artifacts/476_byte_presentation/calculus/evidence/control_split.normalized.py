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
    need(form is None or (size in (2, 1 if form else 3) and (form or size == 3 or a[0] == 0)))
    a = [walk(b, f, d + (2 if size == 1 else int(size == 3 and i == 2)), size == 1) for i, b in enumerate(a)]
    return a

def syntax(a, n, form=False):
    need(walk(a, lambda i, d: need(1 - n <= i <= d) or i, form=form) == a)

def sub(a, t, depth=0):
    return walk(a, lambda i, d: t if i == d + 1 else i - (i > d + 1), depth)

def prove(p, g):
    n = len(g)
    b = -n
    match p:
        case ['u', j, t, q]:
            need(type(j) is int and 0 <= j < n)
            syntax(t, n)
            u, B = g[j]
            if u:
                need(prove(q, g) == u)
            else:
                need(q is None)
            A = sub(B, t)
        case ['e', q, v]:
            D, = prove(q, g)
            B = sub(D, b, 1)
            local = g + [(sub(B, 0), B)]
            A = prove(v, local)
        case ['v', q, r]:
            E = prove(q, g)
            A = prove(r, g)
            match (E, A):
                case [[s, t], [[0, a, h], z]] if s == a:
                    A = [z, t]
                case [[s, t], [[[0, c], a, h], z]] if s == [c, a, h]:
                    A = [z, sub(h, t)]
                case _:
                    need(False)
        case ['i', B0, t, r]:
            syntax(t, n)
            B = sub(B0, t, 1)
            eta = 0
            match B0:
                case [[1, 1, _], [1, 1, _]]:
                    eta = b
            u = sub(B, eta)
            need(prove(r, g + [([], u)]) == sub(B, [0, b]))
            A = [B0]
        case _:
            need(False)
    syntax(A, n, True)
    return A

def check(data):
    need(set(data) == {'goal', 'proof'})
    syntax(data['goal'], 1, True)
    need(prove(data['proof'], [([], [1, 1])]) == data['goal'])
if __name__ == '__main__':
    check(json.load(open(0)))
    print('ACCEPT')
