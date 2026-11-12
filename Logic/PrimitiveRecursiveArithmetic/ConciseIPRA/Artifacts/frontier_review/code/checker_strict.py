import json

def c(a, g=[0], k=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 else a if k <= a < d else d % 2 and i(t, d=3)
    if i(a) in g:
        return
    m, s, u, t = q()
    a = (a, i(t, s))[(m, a) == (s and [s, u] or [t] * 3, i(t, u))]
    h = c(m, g, k) or m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2))
    k -= 1
    c(i(a, [k]), g + [i(h, (m or ~len(a) % 2) and k)], k)

def data_ok(a):
    return type(a) is int or (type(a) is list and all(map(data_ok, a)))

def formula(a, numerical=False):
    if type(a) is int:
        return numerical and (a == 0 or (a >= 3 and a % 2 == 1))
    size = len(a)
    return size in ([1, 3] if numerical else [1, 2]) and all((formula(b, numerical or size == 2) for b in a)) and (numerical or size == 2 or len(a[0]) == 1 or all((b[:2] == [5, 0] for b in a[0])))
p = json.load(open(0))
if type(p) is not list or not data_ok(p):
    raise ValueError('The certificate must be a list containing only integers and lists')
q = p.pop
a = q()
if not formula(a):
    raise ValueError('The goal must be a canonical closed guarded Eq/D formula')
c(a)
print('ACCEPT')
