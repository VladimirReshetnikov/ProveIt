from json import load
k = 0
i = lambda a, t=0j, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 and (k or len(a) in (1, 2 + d % 2)) else a or 1 if k <= a < d and (k or d & a % 2) else (d % 2 or not k) and i(t, d=3)

def c(g, a):
    global k
    s, u, t = r = q()
    if i(a) not in ((k := (~-k)), *g, [[s and [s] or 1, u, t], i(t, r, 3) if s else u]):
        if i(t, u) == a:
            a = i(t, s)
            s = r[:2] if s else [t] * 3
        c([*g, i(s * 3 or (a := i(*a, t, 2)), (c(g, s) or s or len(a) == 2 == u) and k)], i(a, [k]))
p = load(open(0))
q = str(p).strip('0123456789-[], ') or p.pop
c(b'\x00', q())
print('ACCEPT')
