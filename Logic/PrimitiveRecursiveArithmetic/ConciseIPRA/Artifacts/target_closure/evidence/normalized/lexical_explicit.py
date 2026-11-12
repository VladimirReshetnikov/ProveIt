import json

def c(a, g=[0], k=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 == [] else a if k <= a < d else d % 2 and i(t, d=3)
    if i(a) in g:
        return
    m, s, u, t = q()
    a = m == ([s, u] if s else [t] * 3) and i(t, u) == a and i(t, s) or a
    h = c(m, g, k) or m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2))
    k -= 1
    c(i(a, [k]), g + [i(h, (m or len(a) % 2 == u) and k)], k)

def v(a, d=False):
    if a * 0 != []:
        return d and (a == 0 or (a >= 3 and a % 2))
    return len(a) in ([1, 3] if d else [1, 2, 3]) and (d or len(a) != 3 or a == [a[0]] * 3) and all((v(b, d or len(a) == 2) for b in a))
q = open(0).read()
if q.strip('[],-0123456789 \t\r\n'):
    raise ValueError('Only integer/list certificate syntax is allowed')
q = json.loads(q).pop
a = q()
if not v(a):
    raise ValueError('The goal is not a canonical closed formula')
c(a)
print('ACCEPT')
