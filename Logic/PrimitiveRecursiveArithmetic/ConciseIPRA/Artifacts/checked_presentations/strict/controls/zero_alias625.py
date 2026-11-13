import json

def c(g, a, k=0, v=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 and v <= (len(a) in (1, 2 + d % 2)) else a if k <= a < d and v <= d % 2 & a else d % 2 | v and i(t, d=3)
    if i(a) not in g:
        m, s, u, t = q()
        c(g + [i(c(g, m, k, (v := 0)) or m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2)), bool(m or len(a) % 2 == u) * (k := (~-k)))], i((a, i(t, s))[(m, a) == (s and [s, u] or [t] * 3, i(t, u))], [k]), k)
p = json.load(open(0))
q = str(p).strip('0123456789-[], ') or p.pop
c([0, [1, 0]], q(), v=1)
print('ACCEPT')

