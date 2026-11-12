"""Complete Choice-DI checker restricted to QE targets: canonical 1 or variables.

Inherited from scalar_feedback/code/choice_checker.py at the pinned ProveIt
snapshot. The only semantic change is the two-line Q-target guard below.
No producer or test module is imported. See the report for the conservative
proof translation and the inherited sorted-decoder interpretation.
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
            if not m[1:] and not (t == [0] or type(t) is int and k <= t < 0):
                raise ValueError('QE target must be canonical one or an allocated numerical variable')
            s, u, t = m + [t] if m[1:] else [0, t] + m
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
    q = json.load(open(0)).pop
    1 / c(q(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
