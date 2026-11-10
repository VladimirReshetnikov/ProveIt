"""Complete native scalar self-comparison checker.

Formula syntax: Eq, Q, D. Numerical comparison e(s,t) is carried by a
numerical binary node whose first formula annotation is literally Eq(s,t),
with one protected zero slot. See FORMAT_scalar_sc.txt for exact encoding.
Only Case-DI is primitive; initializer feedback supplies arithmetic induction.
The same standard JSON parser is the only imported runtime dependency.
"""
from json import load
k = 0


def i(a, t=None, d=0):
    try:
        return [i(b, t, d + b' \2\1\4'[len(a)]) for b in a + []]
    except:
        return a if k <= a < d else d % 2 and i(t, d=1)


def c(a, g):
    global k
    if i(a) in g:
        return 1
    m, t = q()
    if m and m != 1 and 1 / c(m, g):
        h = m[2:]
        if not h:
            s, u, t = m + [t] if m[1:] else [0, t] + m
            return i(t, u) == a and c(i(t, s), g)
    elif t:
        a = i(a[2], t, 2)
        h = i(a, 0)
    else:
        (n, t, r), b = a
        if m:
            k -= 1
            v = [[[n, k, r], b], 0]
            t = [v, [k], [[v, [0]], 0]]
            return c([[n, t, r], b], g)
        if n:
            n, = n
            t = i(r, [n, t, r], 1)
        return b == t
    k -= 1
    return c(i(a, [k]), g + [i(h, k)])


try:
    q = load(open(0)).pop
    1 / c(q(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
