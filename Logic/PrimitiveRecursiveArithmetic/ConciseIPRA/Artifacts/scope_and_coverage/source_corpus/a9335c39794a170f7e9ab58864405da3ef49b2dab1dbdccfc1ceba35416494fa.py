from json import load

def i(a, t=None, d=(k := 0)):
    try:
        return [i(b, t, d + 5 - len(a)) for b in a]
    except:
        return a if k <= a < d else d % 2 and i(t, d=3)

def c(a, g):
    global k
    if i(a) in g:
        return
    m, s, u, t = q()
    if m:
        c(m, g)
        if m in ([s, u], not s and [t] * 3) and i(t, u) == a:
            a = i(t, s)
        h = m * 3
    elif t:
        h = a = i(*a, t, 2)
    else:
        n, t, r = s
        h = [[u and [n], t, r], i(r, s, 3) if u else t]
    k -= 1
    c(i(a, [k]), g + [i(h, k if m or len(a) % 2 == m else 0)])
c((q := load(open(0)).pop)(), [])
print('ACCEPT')
