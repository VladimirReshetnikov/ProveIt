import json

def c(a, g=[0], k=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 else a if k <= a < d else d % 2 and i(t, d=3)
    if i(a) in g:
        return
    m, s, u, t = q()
    h = c(i(t, s), g, k) or i(t, u) if (s and [s, u] or [t] * 3) in g else c(m, g, k) or m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2))
    k -= 1
    c(i(a, [k]), g + [i(h, (m or ~len(a) % 2) and k)], k)

def formula(a, d=False):
    if type(a) is int:
        return d and (a == 0 or (a >= 3 and a % 2))
    n = len(a)
    return type(a) is list and n in ([1, 3] if d else [1, 2]) and all((formula(b, d or n == 2) for b in a)) and (d or n == 2 or len(a[0]) == 1 or all((b[:2] == [5, 0] for b in a[0])))
q = (p := json.load(open(0))).pop
a = q()
c(a if set(str(p)) <= set('-0123456789[], ') and formula(a) else c)
print('ACCEPT')
