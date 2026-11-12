from json import load
k = 0


i = lambda a, t=None, d=0: [i(b, t, d + b' \2\1\4'[len(a)]) for b in a] if isinstance(a,list) else a if k <= a < d else d % 2 and i(t, d=1)


def c(a, g):
    global k
    if i(a) in g:
        return
    m, s, u, t = q()
    if m:
        c(m, g)
        if m in ([s, u], not s and [t]) and i(t, u) == a:
            a = i(t, s)
    elif t:
        a = i(a[2], t, 2)
    else:
        (n, t, r), b = a
        if n:
            n, = n
            t = i(r, [n, t, r], 1)
        return 1 / (b == t)
    k -= 1
    c(i(a, [k]), g + [i(m[2:] if m else a, k if m or len(a) % 2 == m else 0)])


try:
    c((q := load(open(0)).pop)(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
