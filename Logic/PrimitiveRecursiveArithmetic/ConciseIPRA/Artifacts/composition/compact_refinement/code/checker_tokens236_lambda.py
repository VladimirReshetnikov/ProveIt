from json import loads
k = 0
i = lambda a, t=0j, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 else a if k <= a < d else d % 2 and i(t, d=3)

def c(g, a):
    global k
    s, u, t = r = loads(input())
    if i(a) not in g + [[[s and [s], u, t], i(t, r, 3) if s else u]]:
        if i(t, u) == a:
            a = i(t, s)
            s = r[:2] if s else [t] * 3
        c(g + [i(s * 3 or (a := i(*a, t, 2)), k if c(g, s) or s or len(a) == 2 else 0)], i(a, [k]))
    k -= 1
c(*loads(input()))
print('ACCEPT')
