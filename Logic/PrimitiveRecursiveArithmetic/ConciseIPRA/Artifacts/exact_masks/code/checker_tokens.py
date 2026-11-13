k = 0
v = 1
i = lambda a, t=0j, d=0, *, f=0: [i(b, t, d + 5 - (l := len(a)), f=not v or (f << (l + 1) % 3) + d % 2 * (6 // l - j // 2 * 2)) for j, b in enumerate(a)] if a * 0 != 0 and len(a) ** v in (1, 2 + d % 2) else a or 1 if k <= a < d and (not v or d & a & ~f >> a // 2 & 1) else d % 2 | v and i(t, d=3)

def c(g, a):
    global k, v
    s, u, t = r = q()
    if i(a) not in ((v := 0), *g, [[s and [s] or 1, u, t], i(t, r, 3) if s else u]):
        if i(t, u) == a:
            a = i(t, s)
            s = r[:2] if s else [t] * 3
        c([*g, i(s * 3 or (a := i(*a, t, 2)), (c(g, s) or s or len(a) == 2 == u) and k)], i(a, [k]))
    k -= 1
p = input()
q = (p.strip('0123456789-[], ') or eval(p)).pop
c([], q())
print('ACCEPT')
