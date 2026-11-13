# UNSOUND negative control. Never use as a proof checker.
from json import loads

def i(a, t=0j, d=0):
    try:
        return a if a[3:] else [i(b, t, d + 5 - len(a)) for b in a]
    except:
        return a if a < d else d % 2 and i(t, d=3)

def c(g, a):
    s, u, t = r = loads(input())
    if i(a) not in (*g, [[s and [s], u, t], i(t, r, 3) if s else u]):
        r += [g, a]
        if i(t, u) == a:
            a = i(t, s)
            s = r[:2] if s else [t] * 3
        c([*g, i(s * 3 or (a := i(*a, t, 2)), (c(g, s) or s or len(a) == 2) and [0,0,0,0])], i(a, [[0,0,0,0]]))
c([0], loads(input()))
print('ACCEPT')
