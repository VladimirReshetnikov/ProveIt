import json

def c(p, g=[[]], k=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 == [] else a if k <= a < d else d % 2 and i(t, d=3)
    if type(p) == int:
        return g[p]
    m, s, u, t = p
    m = c(m, g, k)
    if len(m) == 2:
        l, r = c(s, g, k)
        return [r, i(t, m[1], 3)] if l == i(t, m[0], 3) else 1 / 0
    if len(m) == 3:
        return i(m[-1], u) if c(s, g, k) == i(m[-1], 0) else 1 / 0
    if m:
        k -= 1
        a = c(s, g + [i(m * 3, k)], k)
        k += 1
        return i(a)
    if u:
        return i([[s and [s], u, t], i(t, [s, u, t], 3) if s else u])
    w, p = t
    a, b = i(s), i(*s, w, 2)
    k -= 1
    return a if c(p, g + [i(b, (len(b) == 2 and not w) and k)], k) == i(b, [k]) else 1 / 0

p, a = json.load(open(0))
if c(p) == a:
    print('ACCEPT')
