import json

def c(g, a, k=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 else a if k <= a < d else d % 2 and i(t, d=3)
    if i(a) in g:
        return
    m, s, u, t = q()
    c(g + [i(c(g, m, k) or m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2)), bool(m or 3 % len(a)) * (k := (~-k)))], i((m, a) == (s and [s, u] or [t] * 3, i(t, u)) and i(t, s) or a, [k]), k)
q = json.load(open(0)).pop
c([0], q())
print('ACCEPT')
