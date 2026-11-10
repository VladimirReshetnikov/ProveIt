"""Complete all-starts native iPRA proof checker.

Numerical syntax and sorted opening are inherited from Choice-DI.
For an equation matrix E, Q E now means the all-starts closure
forall r,v (E(r) -> E(I(r,v;u.Su))). Other Q matrices retain
B(0) -> forall y B(y). Paired D means exists x Q B(x,y).
Introduction is deterministic: progress at an equation; base at a
compound formula. Atomic-Q elimination payload is the pair [r,v].
Its two endpoints are root-validated before the trajectory is built.
See IMPLEMENTATION.md for the full protocol and branch proof.
Only standard json is imported; input is data, never Python code.
"""
import json
k = 0


i = lambda a, t=None, d=0: [i(b, t, d + b' \2\1\4'[len(a)]) for b in a] if isinstance(a,list) else a if k <= a < d else d % 2 and i(t, d=1)


def c(a, g):
    global k
    if i(a) in g:
        return 1
    m, t = q()
    if m:
        1 / c(m, g)
        try:
            h = [m[2]]
        except:
            u = t
            try:
                s = 0
                t, = m
                if len(t) == 2:
                    s, u = i(u)
                    u = [s, u, [3]]
            except:
                s, u = m
            return i(t, u) == a and c(i(t, s), g)
    elif t:
        h = a = i(a[2], t, 2)
    else:
        (n, t, r), b = a
        if n:
            n, = n
            t = i(r, [n, t, r], 1)
        return b == t
    k -= 1
    return c(i(a, [k]), g + [i(h, k if m or len(a) % 2 == 0 else 0)])


try:
    q = json.load(open(0)).pop
    1 / c(q(), [])
    print('ACCEPT')
except:
    print('REJECT')
    raise SystemExit(1)
