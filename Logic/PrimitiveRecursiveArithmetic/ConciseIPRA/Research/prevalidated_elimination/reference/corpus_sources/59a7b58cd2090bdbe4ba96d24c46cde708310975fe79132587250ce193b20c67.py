"""Experimental complete native iPRA checker with localized induction.

Paired D introduction retains its zero-instance assumption (Case only).
Unary Q introduction is Progress only, and requires a literal equation.
The Eq/Q/D meanings and all elimination rules are inherited unchanged.
This experimental implementation is larger than the Choice-DI benchmark;
its finite tests do not constitute a formal correctness proof.
Adapted from the attributed Choice-DI programs in the inspected ProveIt
corpus, commit 1d0d5f030546d707992b4cc4194ea6971fe84938.
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
            except:
                s, u = m
            return i(t, u) == a and c(i(t, s), g)
    elif t:
        try:
            h, = a
            s, u = h
            a = h
        except:
            a = i(a[2], t, 2)
            h = i(a, 0)
    else:
        (n, t, r), b = a
        if n:
            n, = n
            t = i(r, [n, t, r], 1)
        return b == t
    k -= 1
    return c(i(a, [k]), g + [i(h, k)])


try:
    q = json.load(open(0)).pop
    1 / c(q(), [])
    print('ACCEPT')
except:
    print('REJECT')
    raise SystemExit(1)
