"""Experimental proof-tree kernel with fresh opaque numerical atoms.

The input is [proof, closed_goal]. Every non-hypothesis proof node is
[major, packed_payload, [major_proof, minor_proof, 0]]. A payload is
wrapped in a singleton for a formula motive and in [term, 0] for a
numerical witness. Only the first wrapper member is read by inference;
its other members determine the binding structure of proof substitution.

At DI/DE the kernel opens both the sequent and the continuation proof
with a freshly allocated object. Objects cannot occur in parsed JSON.
This is a research candidate, not yet the delivered verified checker.
"""
import json


def i(a, t=None, d=0):
    try:
        return [i(b, t, d + b' \2\1\4'[len(a)]) for b in a + []]
    except:
        return a if type(a) == object or 0 <= a < d else d % 2 and i(t, d=1)


def c(a, g, p, s=0):
    if i(a) in g:
        return 1
    m, t, (r, p, _) = p
    t = t[0]
    if m and c(m, g, r):
        if [] in (h := [0, m[2:]]):
            u = t
            try:
                t, = m
            except:
                s, u = m
            return i(t, u) == a and c(i(t, s), g, p)
    elif t:
        a = i(a[2], t, 2)
        h = [len(a) % 2 or a, i(a, 0)]
    else:
        (n, t, r), b = a
        if n:
            n, = n
            t = i(r, [n, t, r], 1)
        return b == t
    x = object()
    return c(i(a, [x]), g + i(h, x, -1), i(p, x))


try:
    p, a = json.load(open(0))
    1 / c(a, [], p)
    print('ACCEPT')
except:
    print('REJECT')
    raise SystemExit(1)
