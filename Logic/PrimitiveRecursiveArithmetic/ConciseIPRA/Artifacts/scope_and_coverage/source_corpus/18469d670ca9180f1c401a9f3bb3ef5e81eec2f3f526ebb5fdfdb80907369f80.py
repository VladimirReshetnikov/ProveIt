from json import load
k = 0

def i(a, t=None, d=0):
    try:
        return [i(b, t, d + b' \x02\x01\x04'[len(a)]) for b in a + []]
    except:
        return a if k <= a < d else d % 2 and i(t, d=1)

def c(a, g):
    global k
    if i(a) not in g:
        m, s, u, t = q()
        if m:
            c(m, g)
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
    c((q := load(open(0)).pop)(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
