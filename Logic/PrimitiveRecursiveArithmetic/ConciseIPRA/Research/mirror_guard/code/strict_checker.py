import json

def c(a, g=[[]], k=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 == [] else a if k <= a < d else d % 2 and i(t, d=3)
    if i(a) in g:
        return
    m, s, u, t = q()
    a = m == ([s, u] if s else [t] * 3) and i(t, u) == a and i(t, s) or a
    h = c(m, g, k) or m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2))
    k -= 1
    c(i(a, [k]), g + [i(h, (m or not len(a) % 2) and k)], k)
def term(a, slots):
    if type(a) is int:
        return a == 0 or 3 <= a < 3 + 2 * len(slots) and a % 2 == 1 and slots[(a - 3) // 2]
    return type(a) is list and (len(a) == 1 and term(a[0], (False, False) + slots) or len(a) == 3 and all(term(b, (j == 2,) + slots) for j, b in enumerate(a)))

def raise_slot(a, depth=3):
    if type(a) is list:
        return [raise_slot(b, depth + 5 - len(a)) for b in a]
    return a + 2 if a >= depth else a

def formula(a, slots=()):
    if type(a) is not list:
        return False
    if len(a) == 2:
        return all(term(b, slots) for b in a)
    if len(a) != 1 or not formula(a[0], (True, True) + slots):
        return False
    matrix = a[0]
    if len(matrix) == 1:
        return True
    left, right = matrix
    return type(right) is list and len(right) == 3 and right[0] == 5 and right[1] == raise_slot(left)

q = json.load(open(0)).pop
a = q()
if not formula(a):
    raise ValueError('The goal is not a canonical closed mirrored formula')
c(a)
print('ACCEPT')
