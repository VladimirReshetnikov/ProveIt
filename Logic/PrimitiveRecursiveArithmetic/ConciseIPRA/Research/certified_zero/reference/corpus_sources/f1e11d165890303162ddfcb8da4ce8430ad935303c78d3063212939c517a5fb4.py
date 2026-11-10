"""Complete Choice-DI checker with successor-seeded counter-aware recursion.

Numerical primitives are zero and R. Unary S is the fixed abbreviation
S(a)=R(0,a;u,v.0). The numerical computation rules are
R(0,a;u,v.h)=S(a), R(S(n),a;u,v.h)=h[n/u,R(n,a;u,v.h)/v].
The update environment is (previous state v, counter u, outer parameters).
Eq/Q/D logic and its proof rules are inherited without change.
Only Python's standard json module is imported. See FORMAT.txt.
"""
import json
k = 0
i = lambda a, t=None, d=0: [i(b, t, d + b' \x02\x01\x04'[len(a)]) for b in a] if type(a) is list else a if k <= a < d else d % 2 and i(t, d=1)

def c(a, g):
    global k
    if i(a) in g:
        return 1
    m, t = q()
    if m and 1 / c(m, g):
        h = m[2:]
        if not h:
            s, u, t = m + [t] if m[1:] else [0, t] + m
            return i(t, u) == a and c(i(t, s), g)
    elif t:
        h = a = i(a[2], t, 2)
    else:
        (n, t, r), b = a
        return b == (i(i(r, *n, 3), [*n, t, r], 1) if n else [t])
    k -= 1
    return c(i(a, [k]), g + [i(h, k if m or len(a) % 2 == m else 0)])
try:
    q = json.load(open(0)).pop
    1 / c(q(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
