from json import load

def c(g, a, k=0):
    if (i := (lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 and (g or len(a) in (1, 2 + d % 2)) else a if k <= a < d and (g or d & (a % 2 == (a > 1))) else (d % 2 or not g) and i(t, d=3)))(a) not in g:
        g += [0]
        m, s, u, t = q()
        c(g + [i(c(g, m, k) or m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2)), bool(m or len(a) % 2 == u) * (k := (~-k)))], i((a, i(t, s))[(m, a) == (s and [s, u] or [t] * 3, i(t, u))], [k]), k)
c([], (q := (str((p := load(open(0)))).strip('0123456789-[], ') or p.pop))())
print('ACCEPT')
