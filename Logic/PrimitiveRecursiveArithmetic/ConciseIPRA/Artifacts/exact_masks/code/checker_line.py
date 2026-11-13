def c(g, a):
    global k
    s, u, t, m = r = q()
    i(a) in ((k := (~-k)), *g, [[s and [s] or 1, u, t], i(t, r[:3], 3) if s else u]) or c(g + [i(m * 3 or (a := i(*a, t, 2)), (c(g, m) or m or len(a) == 2 == u) and k)], i((a, i(t, s))[(m, a) == (s and r[:2] or [t] * 3, i(t, u))], [k]))
k = 0
i = lambda a, t=c, d=0, *, f=0: [i(b, t, d + 5 - (l := len(a)), f=k or (f << (l + 1) % 3) + d % 2 * (6 // l - j // 2 * 2)) for j, b in enumerate(a)] if a * 0 != 0 and (k or len(a) in (1, 2 + d % 2)) else a or 1 if k <= a < d and (k or d & a & ~f >> a // 2 & 1) else d % 2 * i(t, d=3)
p = input()
q = (p.strip('0123456789-[], ') or eval(p)).pop
c([[]], q())
print('ACCEPT')
