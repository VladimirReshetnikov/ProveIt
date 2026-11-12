"""Complete iPRA checker with deferred local-assumption selection.

Derived from the pinned Choice-DI checker. Only standard json is imported.
The report specifies the calculus, sorted decoder, proof of correctness,
input protocol, interpretation theorem, and finite-resource limitations.
"""
from json import load
k = 0


def i(a, t=None, d=0):
    try:
        return [i(b, t, d + b' \2\1\4'[len(a)]) for b in a + []]
    except:
        return a if k <= a < d else d % 2 and i(t, d=1)



def c(a, g):
    global k
    if i(a) in g:
        return
    m, t = q()
    if m:
        c(m, g)
        try:
            h = [m[2]]
        except:
            u = t
            try:
                s = 0
                t, = m
            except:
                s, u = m
            1 / (i(t, u) == a)
            return c(i(t, s), g)
    elif t:
        h = a = i(a[2], t, 2)
    else:
        (n, t, r), b = a
        if n:
            n, = n
            t = i(r, [n, t, r], 1)
        return 1 / (b == t)
    k -= 1
    return c(i(a, [k]), g + [i(h, k if m or len(a) % 2 == m else 0)])


try:
    q = load(open(0)).pop
    c(q(), [])
    print('ACCEPT')
except:
    print('REJECT')
    raise
