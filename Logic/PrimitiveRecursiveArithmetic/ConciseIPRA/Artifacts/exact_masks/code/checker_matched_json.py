def c(g, a, k=0):
    s, u, t, m = r = q()
    (i := (lambda a, t=c, d=0, *, v=0: [i(b, t, d + 5 - len(a), v=g or (4 * v + 6 * (d % 2), v, 2 * v + 2 * (j != 2))[len(a) - 1]) for j, b in enumerate(a)] if a * 0 != 0 and (g or len(a) in (1, 2 + d % 2)) else a or 1 if k <= a < d and (g or d & a & ~v >> a // 2 & 1) else d % 2 * i(t, d=3)))(a) in (g.append([]), *g, i([[s and [s], u, t], i(t, r[:3], 3) if s else u])) or c(g + [i(c(g, m, k) or m * 3 or (a := i(*a, t, 2)), any((m, len(a) == 2 == u)) * (k := (~-k)))], i((a, i(t, s))[(m, a) == (s and r[:2] or [t] * 3, i(t, u))], [k]), k)
import json
p = json.load(open(0))
q = str(p).strip('0123456789-[], ') or p.pop
c([], q())
print('ACCEPT')
