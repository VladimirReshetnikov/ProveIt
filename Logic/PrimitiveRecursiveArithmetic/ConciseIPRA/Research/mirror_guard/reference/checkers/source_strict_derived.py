import json

def c(a, g=[[]], k=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 == [] else a if k <= a < d else d % 2 and i(t, d=3)
    if i(a) in g:
        return
    m, s, u, t = q()
    a = m == ([s, u] if s else [t] * 3) and i(t, u) == a and i(t, s) or a
    h = c(m, g, k) or m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2))
    k -= 1
    c(i(a, [k]), g + [i(h, (m or len(a) % 2 == u) and k)], k)
def term(a, slots):
    if type(a) is int:
        return a == 0 or 3 <= a < 3 + 2 * len(slots) and a % 2 == 1 and slots[(a - 3) // 2]
    return type(a) is list and (len(a) == 1 and term(a[0], (False, False) + slots) or len(a) == 3 and all(term(b, (j == 2,) + slots) for j, b in enumerate(a)))

def formula(a, slots=()):
    if type(a) is not list:
        return False
    if len(a) == 2:
        return all(term(b, slots) for b in a)
    return len(a) == 1 and formula(a[0], (True, True) + slots)

q = json.load(open(0)).pop
a = q()
if not formula(a):
    raise ValueError('The goal is not a canonical closed formula')
c(a)
print('ACCEPT')
