import json

def c(g, a, k=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 and (g or len(a) in (1, 2 + d % 2)) else a if k <= a < d and (g or (int(a) is a and d % 2 and (not a or a > 1 == a % 2))) else (d % 2 or not g) and i(t, d=3)
    return i(a) in g or [c((g := [*g, 0]) + [i(c(g, m, k) and m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2)), bool(m or len(a) % 2 == u) * (k := (~-k)))], i(i(t, s) if (m, a) == (s and [s, u] or [t] * 3, i(t, u)) else a, [k]), k) for m, s, u, t in [q()]]
q = json.load(open(0)).pop
c([], q())
print('ACCEPT')
