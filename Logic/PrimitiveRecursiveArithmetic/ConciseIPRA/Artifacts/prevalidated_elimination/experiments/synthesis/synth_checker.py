import json
k = 0
i = lambda a, t=None, d=0: [i(b, t, d + 5 - len(a)) for b in a] if isinstance(a, list) else a if k <= a < d else d % 2 and i(t, d=3)

def c(g):
    global k
    p = q()
    if not isinstance(p, list):
        return g[p]
    m, s, u, t = p
    b = k
    if m:
        m = c(g)
        if len(m) == 1:
            k -= 1
            a = c(g + [i(m * 3, k)])
        else:
            if len(m) == 2:
                s, u = m
            else:
                _, _, t = m
                s = 0
            if c(g) != i(t, s):
                raise ValueError
            a = i(t, u)
    elif u:
        a = [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]
    else:
        a = s
        h = i(*a, t, 2)
        k -= 1
        if c(g + [i(h, k if len(h) % 2 == m else 0)]) != i(h, [k]):
            raise ValueError
    k = b
    return i(a)
q = json.load(open(0)).pop
a = q()
if c([]) != i(a):
    raise ValueError
print('ACCEPT')
