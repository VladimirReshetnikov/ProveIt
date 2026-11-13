from json import load
k = 0


def i(a, t=None, d=0):
    try:
        return [i(b, t, d + b' \2\1\4'[len(a)]) for b in a + []]
    except:
        return a if k <= a < d else d % 2 and i(t, d=1)


def c(a, g, s=0):
    global k
    if i(a) in g:
        return
    m, t = q()
    if m:
        c(m, g)
        u = t
        try:
            try:
                t, = m
            except:
                s, u = m
        except:
            h = m[2:]
        else:
            if i(t, u) == a:
                return c(i(t, s), g)
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
    q = load(open(0)).pop
    c(q(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
