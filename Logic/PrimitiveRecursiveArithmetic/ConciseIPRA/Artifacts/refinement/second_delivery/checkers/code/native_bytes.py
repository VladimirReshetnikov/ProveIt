import json
c = lambda g, a, k=0, v=0: (i := (lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 and v <= (len(a) in (1, 2 + d % 2)) else a if k <= a < d and v <= d % 2 * (int(a) is a and a % 2 == (a > 1)) else d % 2 | v and i(t, d=3)))(a) in g or [c(g + [i(c(g, m, k, (v := 0)) and m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2)), bool(m or len(a) % 2 == u) * (k := (~-k)))], i((a, i(t, s))[(m, a) == (s and [s, u] or [t] * 3, i(t, u))], [k]), k) for m, s, u, t in [q()]]
q = json.load(open(0)).pop
c([0], q(), v=1)
print('ACCEPT')
