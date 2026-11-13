def c(g, a, k=0, v=0):
    m, s, u, t = q()
    (i := (lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 and v <= (len(a) in (1, 2 + d % 2)) else a or 1 if k <= a < d and v <= d & (a is +a and a % 2) else d % 2 | v and i(t, d=3)))(a) in ((v := 0), *g, [[s and [s] or 1, u, t], i(t, [s, u, t], 3) if s else u]) or c(g + [i(c(g, m, k) or m * 3 or (a := i(*a, t, 2)), any((m, len(a) == 2 == u)) * (k := (~-k)))], i((a, i(t, s))[(m, a) == (s and [s, u] or [t] * 3, i(t, u))], [k]), k)
import json
q = json.load(open(0)).pop
c([], q(), v=1)
print('ACCEPT')
