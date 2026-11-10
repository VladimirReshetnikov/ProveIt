from json import load
k = 0
i = lambda a, t=None, d=0: [i(b, t, d + b' \2\1\4'[len(a)]) for b in a] if type(a) is list else a if k <= a < d else d % 2 and i(t, d=1)

def c(g):
    global k
    z = k
    p = q()
    if type(p) is int:
        a = g[p]
    elif len(p) == 3:
        n, t, r = p
        a = [p, t]
        if n:
            n, = n
            a[1] = i(r, [n, t, r], 1)
    elif len(p) == 2:
        a, (t, e) = p
        h = i(a[2], t, 2)
        k -= 1
        1 / (c(g + [i(h, k if len(h) % 2 == e else 0)]) == i(h, [k]))
    else:
        t, = p
        m = c(g)
        h = m[2:]
        if h:
            k -= 1
            a = c(g + [i(h, k)])
        else:
            s, u, t = m + [t] if m[1:] else [0, t] + m
            1 / (c(g) == i(t, s))
            a = i(t, u)
    k = z
    return i(a)
try:
    q = load(open(0)).pop
    1 / (i(q()) == c([]))
except:
    print('REJECT')
    raise
print('ACCEPT')
