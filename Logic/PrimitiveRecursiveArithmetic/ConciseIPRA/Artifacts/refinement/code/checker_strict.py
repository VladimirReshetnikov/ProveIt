import json

def c(g, a, k=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 else a if k <= a < d else d % 2 and i(t, d=3)
    return i(a) in g or [c(g + [i(c(g, m, k) and m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2)), bool(m or 3 % len(a)) * (k := (~-k)))], i((a, i(t, s))[(m, a) == (s and [s, u] or [t] * 3, i(t, u))], [k]), k) for m, s, u, t in [q()]]

def v(a, n=0):
    if a * 0 == 0:
        return n and (a == 0 or (a > 2 and a % 2))
    r = len(a)
    return r in ([1, 3] if n else [1, 2]) and all((v(x, n or r == 2) for x in a)) and (n or r == 2 or len(a[0]) == 1 or all((b[:2] == [5, 0] for b in a[0])))
p = json.load(open(0))
if set(str(p)) - set(' [],-0123456789'):
    raise ValueError
q = p.pop
a = q()
if not v(a):
    raise ValueError
c([0], a)
print('ACCEPT')
