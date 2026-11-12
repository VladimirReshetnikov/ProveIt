import json

def c(p, g=[[]], k=0):
    i = lambda a, t=None, d=0, *, s=c: t if a == s else [i(b, t, d + 5 - len(a), s=s) for b in a] if a * 0 == [] else a if k <= a < d else d % 2 and i(t, d=3)
    if type(p) == int:
        return g[p]
    m, p = p
    m = c(m, g, k)
    if len(m) == 2:
        l, r = c(p, g, k)
        return [r, i(l, m[1], 3, s=m[0])]
    if len(m) == 3:
        p, t = p
        return i(m[-1], t) if c(p, g, k) == i(m[-1], 0) else 1 / 0
    if m:
        k -= 1
        a = c(p, g + [i(m * 3, k)], k)
        k += 1
        return i(a)
    s, u, t = p
    if u:
        return i([[s and [s], u, t], i(t, [s, u, t], 3) if s else u])
    w, p = t
    a, b = i(s), i(*s, w, 2)
    k -= 1
    return a if c(p, g + [i(b, (len(b) == 2 and not w) and k)], k) == i(b, [k]) else 1 / 0

p, a = json.load(open(0))
if c(p) == a:
    print('ACCEPT')
