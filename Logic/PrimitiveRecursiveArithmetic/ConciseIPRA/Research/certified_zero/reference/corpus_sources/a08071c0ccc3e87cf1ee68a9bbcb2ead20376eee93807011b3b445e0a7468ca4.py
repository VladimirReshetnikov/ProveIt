from json import load
k = 0

def i(a, t=None, d=0):
    try:
        return [i(b, t, d + b' \x02\x01\x04'[len(a)]) for b in a + []]
    except:
        return a if k <= a < d else d % 2 and i(t, d=1)

def c(a, g, s=0):
    global k
    m, t = q()
    if m:
        i(m) in g or 1 / c(m, g)
        u = t
        h = m[2:]
        match m:
            case [t]:
                pass
            case [s, u]:
                pass
        if not h:
            return i(t, u) == a and c(i(t, s), g)
    elif t:
        h = a = i(a[2], t, 2)
    else:
        (n, t, r), b = a
        if n:
            n, = n
            t = i(r, [n, t, r], 1)
        return b == t
    k -= 1
    return c(i(a, [k]), g + [i(h, k if m or len(a) % 2 == m else 0)])
try:
    q = load(open(0)).pop
    1 / c(i(q()), [])
    print('ACCEPT')
except:
    print('REJECT')
    raise
