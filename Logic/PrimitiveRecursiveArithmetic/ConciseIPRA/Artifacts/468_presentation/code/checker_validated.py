"""Standalone validated interface for the shifted 468-byte proof kernel.

This larger program makes the compact input promises executable: it checks
all parsed input values, the root framing and floor, and the canonical
closed guarded Eq/D public grammar. It is not a size-record contender.
Unused prefixes may contain arbitrary exact integer/list trees; consumed
instructions are checked by the core's four-field unpacking.
"""
import json


def alphabet(tree):
    return type(tree) is int or type(tree) is list and all(alphabet(x) for x in tree)


def term(tree, slots):
    if type(tree) is int:
        if tree == 0:
            return True
        if tree < 5 or (tree - 5) % 2:
            return False
        index = (tree - 5) // 2
        return index < len(slots) and slots[index]
    if type(tree) is not list:
        return False
    if len(tree) == 1:
        return term(tree[0], (False, False) + slots)
    if len(tree) == 3:
        return (term(tree[0], (False,) + slots)
                and term(tree[1], (False,) + slots)
                and term(tree[2], (True,) + slots))
    return False


def formula(tree, slots=()):
    if type(tree) is not list:
        return False
    if len(tree) == 2:
        return term(tree[0], slots) and term(tree[1], slots)
    if len(tree) == 1:
        body = tree[0]
        if type(body) is list and len(body) == 2:
            # Counter y is slot 0 in the D matrix and slot 1 below the
            # counter's dummy slot, so its exact shifted coordinate is 7.
            if not all(type(side) is list and len(side) == 3
                       and side[0] == 7 and side[1] == 0 for side in body):
                return False
        return formula(body, (True, True) + slots)
    return False


p = json.load(open(0))
if not alphabet(p):
    raise ValueError('The complete certificate must use exact integers and lists')
if type(p) is not list or not p:
    raise ValueError('The certificate must be a nonempty stack')
root = p[-1]
if type(root) is not list or len(root) != 2 or type(root[1]) is not int or root[1] != 0:
    raise ValueError('The last stack item must be [goal,0]')
if not formula(root[0]):
    raise ValueError('The goal must be canonical, closed, guarded, and Q-free')

c = lambda g, a, k: [(i := (lambda a, t=c, d=2: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 else a if k <= a < d else d % 2 * i(t, d=5)))(a) in g + [[[s and [s], u, t], i(t, [s, u, t], 5) if s else u]] or c(g + [i(c(g, m, k) and m * 3 or (a := i(*a, t, 4)), any((m, 3 % len(a))) * (k := (~-k)))], i((a, i(t, s))[(m, a) == (s and [s, u] or [t] * 3, i(t, u))], [k]), k) for m, s, u, t in [q()]]
q = p.pop
c([0], *q())
print('ACCEPT')
