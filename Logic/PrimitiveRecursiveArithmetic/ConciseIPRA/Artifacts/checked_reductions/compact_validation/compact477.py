import json
c = lambda g, a, k: (i := (lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 else a if k <= a < d else d % 2 and i(t, d=3)))(a) in g or [c(g + [i(c(g, m, k) and m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2)), any((m, 3 % len(a))) * (k := (~-k)))], i((a, i(t, s))[(m, a) == (s and [s, u] or [t] * 3, i(t, u))], [k]), k) for m, s, u, t in [q()]]
q = json.load(open(0)).pop
c([0], *q())
print('ACCEPT')
