"""Experimental compact native checker for the three-schema K,J basis.

Parity-dependent opening aligns numerical application with formula equality.
Complete-correctness review and canonical certificate testing are pending.
"""
import json
k = 0


i = lambda a, t=None, d=0: [i(b, t, d + (b' \2\1\4'[len(a)] >> (d % 2))) for b in a] if isinstance(a,list) else a if k <= a < d else d % 2 and i(t, d=1)


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
        h = a = i(a[2], t, 2)
    else:
        p, b = a
        try:
            n, t, r = p
        except:
            (s, n), t = p
            return s == 0 and n == b
        if n:
            s, n = n
            return s == 0 and b == i(r, [n, 0, r], 1)
        return b == 0
    k -= 1
    return c(i(a, [0, k]), g + [i(h, k if m or len(a) % 2 == m else 0)])


try:
    q = json.load(open(0)).pop
    1 / c(q(), [])
    print('ACCEPT')
except:
    print('REJECT')
    raise SystemExit(1)
