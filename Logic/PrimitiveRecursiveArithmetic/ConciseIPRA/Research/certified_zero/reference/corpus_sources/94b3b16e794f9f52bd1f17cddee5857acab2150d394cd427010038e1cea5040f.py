from json import load
k = 0
def i(a, t=None, d=0):
    if type(a) is list:
        a = [i(b, t, d + b' \2\1\4'[len(a)]) for b in a]
        if d == 1 and len(a) == 3 and q():
            n, t, r = a
            if n:
                n, = n
                t = i(r, [n, t, r], 1)
            return i(t, 0, 1)
        return a
    return a if k <= a < d else d % 2 and i(t, d=1)

def c(a, g):
    global k
    a = i(a)
    if a in g:
        return
    m, s, u, t = q()
    if m:
        c(m, g)
        if m in ([s, u], not s and [t]) and i(t, u) == a:
            return c(i(t, s), g)
        h = [m[2]]
    elif t:
        h = a = i(a[2], t, 2)
    else:
        s, u = a
        return 1 / (s == u)
    k -= 1
    c(i(a, [k]), g + [i(h, k if m or len(a) % 2 == m else 0)])
try:
    q = load(open(0)).pop
    c(q(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
