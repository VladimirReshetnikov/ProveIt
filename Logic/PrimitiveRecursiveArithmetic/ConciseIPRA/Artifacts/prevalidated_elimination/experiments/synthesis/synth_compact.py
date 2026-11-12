import json
k = 0
i = lambda a, t=None, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 == [] else a if k <= a < d else d % 2 and i(t, d=3)

def c(g):
    global k
    p = q()
    if p in range(len(g)):
        return g[p]
    m, s, u, t = p
    if m:
        m = c(g)
        if len(m) != 1:
            s, u, t = (0, u, m[2]) if len(m) == 3 else (*m, t)
            [i(t, s)].index(c(g))
            return i(t, u)
        h = m * 3
    elif u:
        return i([[s and [s], u, t], i(t, [s, u, t], 3) if s else u])
    else:
        h = i(*s, t, 2)
    b = k
    k -= 1
    a = c(g + [i(h, k if m or len(h) % 2 == m else 0)])
    [a].index(a if m else i(h, [k]))
    k = b
    return i(a if m else s)
q = json.load(open(0)).pop
s = q()
[c([])].index(i(s))
print('ACCEPT')
