def c(g, a, k):
    s, u, t, m = r = q()
    (i := (lambda a, t=c, d=2: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 else a if k <= a < d else d % 2 * i(t, d=5)))(a) in g + [[[s and [s], u, t], i(t, r[:3], 5) if s else u]] or c(g + [i(c(g, m, k) or m * 3 or (a := i(*a, t, 4)), len(m or a[1:]) % 2 * (k := (~-k)))], i((a, i(t, s))[(m, a) == (s and r[:2] or [t] * 3, i(t, u))], [k]), k)
import json
q = json.load(open(0)).pop
g, a, k = q()
c([0] + g, a, k)
print('ACCEPT')
