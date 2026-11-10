import json
k = 0


i = lambda a, t=None, d=0: [i(b, t, d + b' \2\1\4'[len(a)]) for b in a] if type(a) is list else a if k <= a < d else d % 2 and i(t, d=1)


def c(a, g):
    global k
    m, s, u, t = q()
    if m:
        i(m) in g or c(m, g)
        h = m[2:]
        if m in ([s, u], not s and [t]) and i(t, u) == a:
            a = i(t, s)
    elif t:
        h = a = i(a[2], t, 2)
    else:
        (n, t, r), b = a
        if n:
            n, = n
            t = i(r, [n, t, r], 1)
        if b == t:
            return
    k -= 1
    c(i(a, [k]), g + [i(h, k if m or len(a) % 2 == m else 0)])


try:
    q = json.load(open(0)).pop
    c(i(q()), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
