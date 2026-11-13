def c(g, a):
    global k
    s, u, t, m = r = q()
    i(a) in ((k := (~-k)), *g, [[s and [s] or 1, u, t], i(t, r[:3], 3) if s else u]) or c(g + [i(m * 3 or (a := i(*a, t, 2)), (c(g, m) or m or len(a) == 2 == u) and k)], i((a, i(t, s))[(m, a) == (s and r[:2] or [t] * 3, i(t, u))], [k]))
k = 0
i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 and (k or len(a) in (1, 2 + d % 2)) else a or 1 if k <= a < d and (k or d & a % 2) else d % 2 * i(t, d=3)
p = open(0).read()
q = p.strip('0123456789-[], \n\r\t') or eval(p).pop
c([[]], q())
print('ACCEPT')
