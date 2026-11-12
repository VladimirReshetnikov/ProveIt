"""Complete Choice-DI native iPRA checker.

A paired introduction retains exactly one local assumption. Canonical
instruction heads are 0 for equation induction and [] for base cases.
The numerical syntax, Eq/Q/D meanings, computation and eliminations are
inherited; the certificate interface differs from the original checker.
A truthy elimination major must have a successful proof. See report.pdf
and code/native/FORMAT.txt for the decoding and correctness boundaries.
Only the standard json module is imported by this standalone program.
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
        return 1
    m, t = q()
    if m:
        1 / c(m, g)
        u = t
        try:
            try:
                t, = m
            except:
                s, u = m
        except:
            h = m[2:]
        else:
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
    return c(i(a, [k]), g + [i(h, k if m or len(a) % 2 == m else 0)])


try:
    q = load(open(0)).pop
    1 / c(q(), [])
    print('ACCEPT')
except:
    print('REJECT')
    raise
