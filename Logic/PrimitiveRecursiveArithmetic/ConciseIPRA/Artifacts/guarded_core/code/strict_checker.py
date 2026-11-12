import json

def c(a, g=[[]], k=0):
    i = lambda a, t=0j, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 == [] else a if k <= a < d else d % 2 and i(t, d=3)
    if i(a) in g:
        return
    m, s, u, t = q()
    c(m, g, k)
    a = m in ([s, u], not s and [t] * 3) and i(t, u) == a and i(t, s) or a
    h = m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2))
    k -= 1
    c(i(a, [k]), g + [i(h, (m or not len(a) % 2) and k)], k)

def term(a, slots):
    if type(a) is int:
        return a == 0 or (3 <= a < 3 + 2 * slots and a % 2 == 1)
    return type(a) is list and (len(a) == 1 and term(a[0], slots + 2) or (len(a) == 3 and all((term(b, slots + 1) for b in a))))

def formula(a, slots=0):
    if type(a) is not list:
        return False
    if len(a) == 2:
        return all((term(b, slots) for b in a))
    if len(a) != 1 or not formula(a[0], slots + 2):
        return False
    matrix = a[0]
    return len(matrix) == 1 or all((type(b) is list and len(b) == 3 and (b[:2] == [5, 0]) for b in matrix))
q = json.load(open(0)).pop
a = q()
if not formula(a):
    raise ValueError('The goal is not a canonical closed guarded formula')
c(a)
print('ACCEPT')
