from json import load
k = 0
v = 1
i = lambda a, t=0j, d=0, *, m=-1: [i(b, t, d + 5 - len(a), m=4 * m - 3 if len(a) == 1 else -m if m < 0 else 2 * m + 2 * (j == 2) - 1) for j, b in enumerate(a)] if a * 0 != 0 and len(a) ** v in (1, 2 + d % 2) else a or 1 if k <= a < d and v <= d & m >> a // 2 * v & a % 2 else d % 2 | v and i(t, d=3)

def c(g, a):
    global k, v
    s, u, t = r = q()
    if i(a) not in ((v := 0), *g, [[s and [s] or 1, u, t], i(t, r, 3) if s else u]):
        if i(t, u) == a:
            a = i(t, s)
            s = r[:2] if s else [t] * 3
        c([*g, i(s * 3 or (a := i(*a, t, 2)), (c(g, s) or s or len(a) == 2 == u) and k)], i(a, [k]))
    k -= 1
p = load(open(0))
q = str(p).strip('0123456789-[], ') or p.pop
c([], q())
print('ACCEPT')
