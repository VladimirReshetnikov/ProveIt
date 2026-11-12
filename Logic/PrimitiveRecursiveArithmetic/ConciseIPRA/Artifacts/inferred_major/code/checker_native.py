import json

def c(a, g=[0], k=0, v=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 == [] and v <= (len(a) in (1, 2 + d % 2)) else a if k <= a < d and v <= (type(a) is int and d % 2 and (not a or a > 1 == a % 2)) else d % 2 | v and i(t, d=3)
    if i(a) in g:
        return
    v = 0
    m, s, u, t = q()
    h = c(m, g, k) or m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2))
    c(i(m == ([s, u] if s else [t] * 3) and i(t, u) == a and i(t, s) or a, [(k := (k - 1))]), g + [i(h, (m or len(a) % 2 == u) and k)], k)
q = json.load(open(0)).pop
c(q(), v=1)
print('ACCEPT')
