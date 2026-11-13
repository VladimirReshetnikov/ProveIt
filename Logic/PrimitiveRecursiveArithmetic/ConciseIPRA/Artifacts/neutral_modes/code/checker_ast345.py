from json import load

def c(g, a, k=0):
    if (i := (lambda a, t=0j, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 and (g or len(a) in (1, 2 + d % 2)) else a or 1 if k <= a < d and (g or d & a % 2) else d % 2 * i(t, d=3)))(a) not in g:
        match q():
            case [m, s, u, t]:
                g += [[]]
        c(g + [i(c(g, m, k) or m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2)), (1 if m else len(a) % 2 == u) * (k := (~-k)))], i(i(t, s) if (m, a) == ([s, u] if s else [t] * 3, i(t, u)) else a, [k]), k)
c([], (q := (str((p := load(open(0)))).strip('0123456789-[], ') or p.pop))())
print('ACCEPT')
