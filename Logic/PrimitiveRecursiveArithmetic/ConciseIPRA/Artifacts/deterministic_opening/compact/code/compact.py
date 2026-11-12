import json

def c(a, g=[0], k=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 else a if k <= a < d else d % 2 and i(t, d=3)
    if i(a) in g:
        return
    m, s, u, t = q()
    h = c(m, g, k) or m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2))
    c(i((m, a) == (s and [s, u] or [t] * 3, i(t, u)) and i(t, s) or a, [(k := (k - 1))]), g + [i(h, (m or ~len(a) % 2) and k)], k)
q = json.load(open(0)).pop
c(q())
print('ACCEPT')
