i = lambda a, t=0j, d=(k := 0), *, f=-2: [i(b, t, d + 5 - (l := len(a)), f=k or (f << (l + 1) % 3) + d % 2 * (6 // l - j // 2 * 2)) for j, b in enumerate(a)] if a * 0 != 0 and (k or len(a) in (1, 2 + d % 2)) else a or 1 if (k <= a < d if k else d & a & ~f >> a // 2 & 1) else (d % 2 or not k) and i(t, d=3)

def c(g, a):
    match q():
        case [s, u, t] as r:
            global k
    if i(a) not in ((k := (~-k)), *g, [[s and [s] or 1, u, t], i(t, r, 3) if s else u]):
        if i(t, u) == a:
            a = i(t, s)
            s = r[:2] if s else [t] * 3
        c([*g, i(s * 3 or (a := i(*a, t, 2)), (c(g, s) or s or len(a) == 2 == u) and k)], i(a, [k]))
c(b'\x00', (q := ((p := input()).strip('0123456789-[], ') or eval(p)).pop)())
print('ACCEPT')
