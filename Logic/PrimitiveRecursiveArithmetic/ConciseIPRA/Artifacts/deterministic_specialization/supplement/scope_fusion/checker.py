import json

def c(a, g=[0], k=0, v=0):
    i = lambda a, t=c, d=0: ([i(b, t, d + 5 - len(a)) for b in a] if not v or len(a) in (1, 2 + d % 2) or a == [a[0]] * 3 else i(c)) if a * 0 != 0 else a if k <= a < d and (not v or d % 2 and (not a or a > 2 and a % 2)) else (v or d % 2) and i(t, d=3)
    if i(a) in g:
        return
    v = 0
    m, s, u, t = q()
    a = m == ([s, u] if s else [t] * 3) and i(t, u) == a and i(t, s) or a
    h = c(m, g, k) or m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2))
    k -= 1
    c(i(a, [k]), g + [i(h, (m or len(a) % 2 == u) and k)], k)

q = json.load(open(0))
if repr(q).strip('0123456789[], -'):
    raise ValueError('The certificate must use integer/list syntax and have a canonical closed goal')
q = q.pop
c(q(), v=1)
print('ACCEPT')


