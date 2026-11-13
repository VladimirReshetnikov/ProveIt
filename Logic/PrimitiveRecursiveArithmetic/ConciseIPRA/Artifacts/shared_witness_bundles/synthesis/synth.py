import json


def need(p):
    if not p:
        raise ValueError('invalid proof')


def term(a, n, d=0):
    if type(a) is int:
        need(-n <= a < d)
        return a
    need(len(a) in (0, 1, 3))
    return [term(b, n, d + (len(a) == 3 and j == 2)) for j, b in enumerate(a)]


def formula(a, n, d=0):
    w, s, t = a
    need(all(k in (1, 2) for k in w))
    return [w, term(s, n, d + sum(w)), term(t, n, d + sum(w))]


def sub(a, t, d=0):
    if type(a) is int:
        return a if a < d else t if a == d else a - 1
    return [sub(b, t, d + (len(a) == 3 and j == 2)) for j, b in enumerate(a)]


def opened(a, *xs):
    w, s, t = a
    d = sum(w)
    for x in xs:
        d -= 1
        s, t = sub(s, x, d), sub(t, x, d)
    return [[w[0] - len(xs)] * (w[0] > len(xs)) + w[1:], s, t]


def check(p, g, n):
    k, *r = p
    if k == 0:
        j, = r
        return g[j]
    if k in (1, 2):
        c, a, h = r
        c, a, h = term(c, n), term(a, n), term(h, n, 1)
        return [[], [[], a, h], a] if k == 1 else [[], [[c], a, h], sub(h, [c, a, h])]
    if k == 3:
        h, p, q = r
        h = term(h, n, 1)
        u, s, t = check(p, g, n)
        v, b, a = check(q, g, n)
        need(u == v == [] and b == sub(h, s))
        return [[], a, sub(h, t)]
    if k == 4:
        p, q, t = r
        a = check(p, g, n)
        need(a[0][0] == 1 and check(q, g, n) == opened(a, []))
        return opened(a, term(t, n))
    if k == 5:
        p, q = r
        a = check(p, g, n)
        need(a[0][0] == 2)
        return formula(check(q, g + [opened(a, -n - 1)], n + 1), n)
    if k == 6:
        t, b, p = r
        t, b = term(t, n), formula(b, n, 2)
        a = [[2] + b[0], *b[1:]]
        need(check(p, g + [opened(a, t, [])], n + 1) == opened(a, t, [-n - 1]))
        return a
    if k == 7:
        b, p = r
        b = formula(b, n, 1)
        need(b[0] == [])
        a = [[1], *b[1:]]
        need(check(p, g + [opened(a, -n - 1)], n + 1) == opened(a, [-n - 1]))
        return a
    raise ValueError('invalid instruction')


p = json.load(open(0))
need(not str(p).strip('0123456789-[], '))
print(json.dumps(check(p, [], 0)))
