import json

def c(a, g=[0], k=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 else a if k <= a < d else d % 2 and i(t, d=3)
    if i(a) in g:
        return
    m, s, u, t = q()
    a = m == ([s, u] if s else [t] * 3) and i(t, u) == a and i(t, s) or a
    h = c(m, g, k) or m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2))
    k -= 1
    c(i(a, [k]), g + [i(h, (m or len(a) % 2 == u) and k)], k)

def v(a, d=0):
    return not d or (d % 2 and (not a or (2 < a < d - 2 and a % 2))) if type(a) is int else a * 0 == [] and (not d or len(a) in (1, 2 + d % 2) or a == [a[0]] * 3) and all((v(b, d and d + 5 - len(a)) for b in a))
q = json.load(open(0))
if not v(q):
    raise ValueError('Only integer/list certificate syntax is allowed')
q = q.pop
a = q()
if not v(a, 2):
    raise ValueError('The goal is not a canonical closed formula')
c(a)
print('ACCEPT')
