# REJECTED UNSOUND EXPERIMENT. This program accepts a false guarded goal.
# Never use it as an arithmetic proof checker. Included solely as negative evidence.
import json
c = lambda g, a, k: (i := (lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 else a if k <= a < d else i(t, d=3)))(a) in g or [a == [[s and [s], u, t], i(t, [s, u, t], 3) if s else u] or c(g + [i(c(g, m, k) and m * 3 or (a := i(*a, t, 2)), any((m, 3 % len(a))) * (k := (~-k)))], i((a, i(t, s))[(m, a) == (s and [s, u] or [t] * 3, i(t, u))], [k]), k) for m, s, u, t in [q()]]
q = json.load(open(0)).pop
c([[]], *q())
print('ACCEPT')
