"""Composition of supplied boxed instructions, context blocks, and elimination.

Canonical introduction witnesses use beta(v)=I(0,v;0) and the inherited
transport construction. Each context extension has two formulas and is
opened through one binary block, starting at depth -1. The substitution
traversal uses copy(), so strings and nonempty objects reject as in the
boxed baseline. No project module, producer, or oracle is imported.
"""
import json
k = 0


def inst(a, t=None, d=0):
    try:
        return [inst(b, t, d + b'\0\2\1\4'[len(a)]) for b in a.copy()]
    except:
        return a if k <= a < d else d % 2 and inst(t, d=1)


def check(a, g):
    global k
    if inst(a) in g:
        return 1
    m, t = take()
    if m and check(m, g):
        if [] in (h := [0, m[2:]]):
            try:
                s, u = m
            except:
                s, u, t = 0, t, *m
            return inst(t, u) == a and check(inst(t, s), g)
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
