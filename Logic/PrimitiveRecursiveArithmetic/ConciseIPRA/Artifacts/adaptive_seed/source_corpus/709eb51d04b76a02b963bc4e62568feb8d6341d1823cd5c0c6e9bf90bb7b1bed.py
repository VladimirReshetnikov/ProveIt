"""Array-only native checker with an equivalent arity-dispatch refactor.

See strict_refinement.tex. No syntax aliases are added. The all-input
equivalence is under ordinary execution with adequate resources.
"""
import json
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
    if m and c(m, g):
        u = t
        try:
            try:
                t, = m
            except:
                s, u = m
        except:
            h = [0, m[2:]]
        else:
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
