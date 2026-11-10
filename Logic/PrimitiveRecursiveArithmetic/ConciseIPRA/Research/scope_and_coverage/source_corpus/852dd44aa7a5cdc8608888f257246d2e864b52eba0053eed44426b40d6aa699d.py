"""Unvalidated compact left-motive size experiment; not a delivered checker.

It inherits the 306-token runtime-dependent iterable decoder. The experiment
only measures the cost of packaging a numerical motive into the existing
shared equality/closure branch; 316 tokens exceed the baseline. No soundness
or all-input equivalence claim is attached to this experiment.
"""
import json
k = 0


def i(a, t=None, d=0):
    try:
        return [i(b, t, d + b' \2\1\4'[len(a)]) for b in a]
    except:
        return a if k <= a < d else d % 2 and i(t, d=1)


def c(a, g, s=0):
    global k
    if i(a) in g:
        return 1
    m, t = q()
    if m and c(m, g):
        if [] in (h := [0, m[2:]]):
            u = t
            try:
                t, = m
            except:
                s, u = m
                t = [t, a[1]]
            return i(t, u) == a and c(i(t, s), g)
    elif t:
        a = i(a[2], t, 2)
        h = [len(a) % 2 or a, i(a, 0)]
    else:
        (n, t, r), b = a
        if n:
            n, = n
            t = i(r, [n, t, r], 1)
        return b == t
    k -= 1
    return c(i(a, [k]), g + i(h, k, -1))


try:
    q = json.load(open(0)).pop
    1 / c(q(), [])
    print('ACCEPT')
except:
    print('REJECT')
    raise SystemExit(1)
