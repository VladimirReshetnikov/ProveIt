import json
c = lambda g, a, k: [(i := (lambda a, t=c, d=2: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 else a if k <= a < d else d % 2 * i(t, d=5)))(a) in g + [[[s and [s], u, t], i(t, [s, u, t], 5) if s else u]] or c(g + [i(c(g, m, k) and m * 3 or (a := i(*a, t, 4)), any((m, 3 % len(a))) * (k := (~-k)))], i((a, i(t, s))[(m, a) == (s and [s, u] or [t] * 3, i(t, u))], [k]), k) for m, s, u, t in [q()]]
q = json.load(open(0)).pop
c([0], *q())
print('ACCEPT')
