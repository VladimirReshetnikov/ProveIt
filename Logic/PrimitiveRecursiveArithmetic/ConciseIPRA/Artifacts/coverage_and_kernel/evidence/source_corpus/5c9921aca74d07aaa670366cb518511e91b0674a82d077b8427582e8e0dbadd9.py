"""Complete initialized-scalar Choice-DI checker with uniform continuation.

Eq/Q elimination shares the eigenparameter/context continuation with D rules.
A failed target match becomes scalar zero, which has no successful finite
checking trace under the list-context invariant. See the accompanying report.
Only standard json is imported. Rejection may include a stderr traceback.
"""
import json
k = 0
i = lambda a, t=None, d=0: [i(b, t, d + b' \x02\x01\x04'[len(a)]) for b in a] if type(a) is list else a if k <= a < d else d % 2 and i(t, d=1)

def c(a, g):
    global k
    if i(a) in g:
        return
    m, t = q()
    if m:
        c(m, g)
        h = m[2:]
        if not h:
            s, u, t = m + [t] if m[1:] else [0, t] + m
            1 / (i(t, u) == a)
            a = i(t, s)
    elif t:
        h = a = i(a[2], t, 2)
    else:
        (n, t, r), b = a
        if n:
            n, = n
            t = i(r, [n, t, r], 1)
        return 1 / (b == t)
    k -= 1
    return c(i(a, [k]), g + [i(h, k if m or len(a) % 2 == m else 0)])
try:
    q = json.load(open(0)).pop
    c(q(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
