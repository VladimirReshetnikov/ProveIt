"""Standalone strict guarded-goal companion to bytes488.py.

All certificate syntax is exact integer/list data. The public goal is checked
against the closed guarded Eq/D grammar before the proof kernel runs.
This larger module is not a coordinate-record profile.
"""
import json

def integer_list_tree(value):
    return type(value) is int or (
        type(value) is list and all(integer_list_tree(x) for x in value)
    )


def public_term(tree, slots):
    if type(tree) is int:
        return tree == 0 or (3 <= tree < 3 + 2 * slots and tree % 2 == 1)
    return type(tree) is list and (
        len(tree) == 1 and public_term(tree[0], slots + 2)
        or len(tree) == 3 and all(public_term(x, slots + 1) for x in tree)
    )


def public_formula(tree, slots=0):
    if type(tree) is not list:
        return False
    if len(tree) == 2:
        return all(public_term(x, slots) for x in tree)
    if len(tree) != 1 or not public_formula(tree[0], slots + 2):
        return False
    matrix = tree[0]
    return len(matrix) == 1 or all(
        type(side) is list and len(side) == 3 and side[:2] == [5, 0]
        for side in matrix
    )


def c(g, a, k=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 else a if k <= a < d else d % 2 and i(t, d=3)
    return i(a) in g or [c(g + [i(c(g, m, k) and m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2)), bool(m or 3 % len(a)) * (k := (~-k)))], i((a, i(t, s))[(m, a) == (s and [s, u] or [t] * 3, i(t, u))], [k]), k) for m, s, u, t in [q()]]
p = json.load(open(0))
if type(p) is not list or not integer_list_tree(p):
    raise ValueError("Expected a JSON array of exact integers and arrays")
q = p.pop
a = q()
if not public_formula(a):
    raise ValueError("Expected a canonical closed guarded Eq/D formula")
c([0], a)
print("ACCEPT")
