"""Dimensions of marked crossingless closures; not a cobordism evaluator."""
from __future__ import annotations
from math import comb

def validate_matching(matching):
    n = len(matching)
    if n == 0 or n % 2: raise ValueError("positive even boundary size required")
    for i,j in enumerate(matching):
        if type(j) is not int or not 0 <= j < n or j == i or matching[j] != i:
            raise ValueError("not a fixed-point-free pairing involution")
    pairs = [(i,j) for i,j in enumerate(matching) if i < j]
    if any(i < k < j < l or k < i < l < j for i,j in pairs for k,l in pairs):
        raise ValueError("matching is not planar in the supplied boundary order")


def closure_circles(matching, closure_matching):
    validate_matching(matching); validate_matching(closure_matching)
    if len(matching) != len(closure_matching): raise ValueError("boundary lengths differ")
    seen = set(); c = 0
    for v in range(len(matching)):
        if v in seen: continue
        c += 1; todo = [v]; seen.add(v)
        while todo:
            u = todo.pop()
            for w in (matching[u],closure_matching[u]):
                if w not in seen: seen.add(w); todo.append(w)
    return c


def reduced_closure_dimension(matching, closure_matching, shift=0, quantum=None):
    """Mark lies on a boundary interval, giving one distinguished circle.

    Grading convention: marked factor has reduced degree zero; unmarked
    circles have basis degrees +1,-1; the object is shifted by `shift`.
    """
    if type(shift) is not int or (quantum is not None and type(quantum) is not int):
        raise ValueError("gradings must be integers")
    d = closure_circles(matching,closure_matching)-1
    if quantum is None: return 1 << d
    twice_r = shift+d-quantum
    return comb(d,twice_r//2) if 0 <= twice_r <= 2*d and twice_r % 2 == 0 else 0
