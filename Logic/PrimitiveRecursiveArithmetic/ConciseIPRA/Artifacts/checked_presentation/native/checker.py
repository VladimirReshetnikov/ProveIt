import json

def c(a, g=[0], k=0, v=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 and (not v or len(a) in (1, 2 + d % 2)) else a if k <= a < d and (not v or (d % 2 and (not a or a > 1 == a % 2))) else (d % 2 or v) and i(t, d=3)
    if i(a) in g:
        return
    v = 0
    m, s, u, t = q()
    h = c(m, g, k) or m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2))
    c(i((a, i(t, s))[(m, a) == (s and [s, u] or [t] * 3, i(t, u))], [(k := (~-k))]), g + [i(h, (m or len(a) % 2 == u) and k)], k)
p = json.load(open(0))
q = not str(p).strip('0123456789-[], ') and p.pop
c(q(), v=1)
print('ACCEPT')
