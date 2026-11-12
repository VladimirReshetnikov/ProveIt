"""Complete initialized-scalar Choice-DI checker with uniform continuation.

Eq/Q elimination shares the eigenparameter/context continuation with D rules.
A failed target match becomes scalar zero, which has no successful finite
checking trace under the list-context invariant. See the accompanying report.
Only standard json is imported. Rejection may include a stderr traceback.
"""
from json import load
k = 0
def i(a, t=None, d=0):
    try:
        return [i(b, t, d + b' \2\1\4'[len(a)]) for b in a + []]
    except:
        return a if k <= a < d else d % 2 and i(t, d=1)

def c(a, g, s=0):
    global k
    if i(a) in g:
        return
    m, t = q()
    if m:
        c(m, g)
        h = m[2:]
        if not h:
            u = t
            try:
                t, = m
            except:
                s, u = m
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
    q = load(open(0)).pop
    c(q(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
