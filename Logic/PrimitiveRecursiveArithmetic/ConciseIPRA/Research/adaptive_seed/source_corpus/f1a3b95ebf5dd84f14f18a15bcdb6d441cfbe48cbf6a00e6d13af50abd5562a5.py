from json import load
k = 0
i = lambda a, t=None, d=0: [i(b, t, d + b' \x02\x01\x04'[len(a)]) for b in a] if isinstance(a, list) else a if k <= a < d else d % 2 and i(t, d=1)

def c(a, g):
    global k
    if i(a) in g:
        return
    m, s, t = q()
    if m:
        c(m, g)
        h = m[2:]
        if len(m) == 2:
            s, u = m
            if t:
                h = i([[s, *t], [u, *t]])
            else:
                x, y = a
                if x == u:
                    a = [s, y]
        elif not h and i(m[0], t) == a:
            a = i(m[0], 0)
    elif t:
        h = a = i(a[2], t, 2)
    else:
        n, t, u = s = i(s, d=1)
        h = i([s, i(i(u, *n, 3), [*n, t, u], 1) if n else [t]])
    k -= 1
    c(i(a, [k]), g + [i(h, k if m or len(a) % 2 == m else 0)])
try:
    q = load(open(0)).pop
    c(q(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
