def c(g, a):
    global k
    s, u, t, m = r = q()
    i(a) in ((k := (~-k)), *g, [[s and [s] or 1, u, t], i(t, r[:3], 3) if s else u]) or c(g + [i(m * 3 or (a := i(*a, t, 2)), (c(g, m) or m or len(a) == 2 == u) and k)], i((a, i(t, s))[(m, a) == (s and r[:2] or [t] * 3, i(t, u))], [k]))
k = 0
i = lambda a, t=c, d=0: [i(b, t, d + (2 * (j == 2) if d % 2 else 5 - len(a))) for j, b in enumerate(a)] if a * 0 != 0 and (k or len(a) in (1, 2 + d % 2)) else a or 1 if k <= a < d and (k or d & a % 2) else d % 2 * i(t, d=3)
import json
p = json.load(open(0))
q = str(p).strip('0123456789-[], ') or p.pop
c([[]], q())
print('ACCEPT')
