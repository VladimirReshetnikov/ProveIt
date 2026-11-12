"""Structural profile of the composed boxed-instruction iPRA checker.

A singleton closure major is normalized before elimination dispatch.
Context extensions use the same two-formula blocks as checker.py.
The a + [] guard traverses only JSON arrays; all strings and objects
reject when traversed. Canonical witness boxing is beta(v)=I(0,v;0),
with the inherited equality transports, not an inert binary zero.
No project module, producer, or oracle is imported.
"""
import json
k = 0


def inst(a, t=None, d=0):
    try:
        return [inst(b, t, d + b'\0\2\1\4'[len(a)]) for b in a + []]
    except:
        return a if k <= a < d else d % 2 and inst(t, d=1)


def check(a, g):
    global k
    if inst(a) in g:
        return 1
    m, t = take()
    if m and check(m, g):
        match m:
            case [b]:
                m, t = [0, t], b
        if [] in (h := [0, m[2:]]):
            return inst(t, m[1]) == a and check(inst(t, m[0]), g)
    elif t:
        a = inst(a[2], t, 2)
        h = [len(a) % 2 or a, inst(a, 0)]
    else:
        (n, t, r), b = a
        if n:
            n, = n
            t = inst(r, [n, t, r], 1)
        return b == t
    k -= 1
    return check(inst(a, [k]), g + inst(h, k, -1))


try:
    take = json.load(open(0)).pop
    1 / check(take(), [])
    print('ACCEPT')
except:
    print('REJECT')
    raise SystemExit(1)
