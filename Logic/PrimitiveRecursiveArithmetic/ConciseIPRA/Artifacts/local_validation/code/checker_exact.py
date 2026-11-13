import json
k = 0
i = lambda a, t=0j, d=0: [i(b, t, d + (j & 2 if d % 2 else 5 - len(a))) for j, b in enumerate(a)] if a * 0 == [] and k | (len(a) in (1, 2 + d % 2)) else a or 1 if k <= a < d and k < d & a % 2 else d % 2 * i(t, d=3)

def c(g, a):
    global k
    s, u, t = r = q()
    i(a) in ((k := (k - 1)), *g, [[[s] if s else 1, u, t], i(t, r, 3) if s else u]) or (i(t, u) != a or ((a := i(t, s)), (s := (r[:2] if s else [t] * 3))), c([*g, i(s * 3 or (a := i(*a, t, 2)), (c(g, s) or s or len(a) == 2 == u) and k)], i(a, [k])))
q = json.load(open(0)).pop
c([[]], q())
print('ACCEPT')
