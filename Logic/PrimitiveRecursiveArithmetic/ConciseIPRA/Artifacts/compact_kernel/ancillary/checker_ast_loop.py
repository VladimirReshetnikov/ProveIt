from json import load

def i(a, t=None, d=(k := 0)):
    try:
        return [i(b, t, d + 5 - len(a)) for b in a]
    except:
        return a if k <= a < d else d % 2 and i(t, d=3)

def c(a, g):
    global k
    while i(a) not in g:
        m, s, u, t = q()
        if m:
            c(m, g)
            if m in ([s, u], not s and [t] * 3) and i(t, u) == a:
                a = i(t, s)
            h = m * 3
        elif m is None:
            h = [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]
        else:
            h = a = i(*a, t, 2)
        k -= 1
        g += (i(h, k if m or len(a) % 2 == m else 0),)
        a = i(a, [k])
c((q := load(open(0)).pop)(), ())
print('ACCEPT')
