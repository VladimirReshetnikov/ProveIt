def term(a, available=()):
    if type(a) is int:
        return a == 1 or (a >= 3 and a % 2 == 1 and ((a - 3) // 2 < len(available)) and available[(a - 3) // 2])
    if type(a) is not list:
        return False
    if len(a) == 1:
        return term(a[0], (False, False) + available)
    if len(a) == 3:
        return term(a[0], (False,) + available) and term(a[1], (False,) + available) and term(a[2], (True,) + available)
    return False

def formula(a, available=()):
    if type(a) is not list:
        return False
    if len(a) == 1:
        return formula(a[0], (True, True) + available)
    if len(a) == 2:
        return term(a[0], available) and term(a[1], available)
    return False

def c(g, a, k=0):
    s, u, t, m = r = q()
    (i := (lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 and (g or len(a) in (1, 2 + d % 2)) else a or 1 if k <= a < d and (g or d & a % 2) else d % 2 * i(t, d=3)))(a) in (g.append([]), *g, i([[s and [s], u, t], i(t, r[:3], 3) if s else u])) or c(g + [i(c(g, m, k) or m * 3 or (a := i(*a, t, 2)), any((m, len(a) == 2 == u)) * (k := (~-k)))], i((a, i(t, s))[(m, a) == (s and r[:2] or [t] * 3, i(t, u))], [k]), k)
import json
p = json.load(open(0))
q = str(p).strip('0123456789-[], ') or p.pop
if type(p) is not list or not p or (not formula(p[-1])):
    raise ValueError('The public goal must be a canonical closed Eq/D formula')
c([], q())
print('ACCEPT')
