from json import load
k = 0

def i(a, t=None, d=0):
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
    h = m * 3 if m else [[s and [s], u, t], i(t, [s, u, t], 3) if s else u] if m is None else (a := i(*a, t, 2))
    k -= 1
    c(i(a, [k]), g + [i(h, (m or len(a) % 2 == m) and k)])
q = load(open(0)).pop
c(q(), [])
print('ACCEPT')
