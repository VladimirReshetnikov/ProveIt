#!/usr/bin/env python3
"""Optional equality-free EPSC1+BU schema for the two-operation kernel.

The mathematical calibration and fusion are PRIOR ProveIt incoming work:
docs/incoming/zfc_unary_closure_research.zip at 61e77836565f63582561f54745f633d50efd9c7d.
This module materializes that schema in the new kernel's bound/free syntax.
The main conservative frontend remains fixed_theory.check_refutation (CP+GIC).
"""
from __future__ import annotations

from itertools import product

import two_kernel as k
from fixed_theory import (Forall, Exists, Or, NamedRel, Subset,
                          decode_candidate, shortlex_bytes_at)


def binary_union():
    a, b, c, y = -4, -3, -2, -1
    body = k.Iff(NamedRel(y, c), Or(NamedRel(y, a), NamedRel(y, b)))
    return Forall(a, Forall(b, Exists(c, Forall(y, body))))


BU = binary_union()


def axiom(matrix):
    """Free slots:0=input x,1=output y,2=parameter p; binders unrestricted."""
    matrix = k.freeze(matrix)
    if not k.scoped(matrix) or not k.free_names(matrix) <= {0, 1, 2}:
        raise ValueError('unary matrices have only free slots 0,1,2')
    x, y, b, c, z, p = range(3, 9)

    def at(a, output):
        return k.rename(matrix, lambda n: a if n == 0 else output if n == 1 else p)

    bounded = Forall(x, Exists(b, Forall(y, k.Imp(at(x, y), Subset(y, b, z)))))
    empty = Forall(z, k.Not(NamedRel(z, x)))
    guarded = k.Imp(Or(empty, NamedRel(x, c)), k.Imp(at(x, y), NamedRel(y, c)))
    closed = Forall(x, Forall(y, guarded))
    support = Forall(y, k.Imp(NamedRel(y, c), Exists(x, at(x, y))))
    hull = Exists(c, k.And(closed, support))
    result = Forall(p, k.Imp(bounded, k.And(BU, hull)))
    if not k.scoped(result) or k.free_names(result):
        raise AssertionError('schema wrapper did not bind every free slot')
    return result


def direct(matrix, domain, relation):
    """Independent quantified specification for finite-model regression checks."""
    subset = lambda a, b: all(not relation(z, a) or relation(z, b) for z in domain)
    empty = lambda x: all(not relation(z, x) for z in domain)
    union = all(any(all(relation(y, c) == (relation(y, a) or relation(y, b))
                            for y in domain) for c in domain)
                for a, b in product(domain, repeat=2))
    for p in domain:
        def rho(x, y):
            return k.evaluate(matrix, domain, relation, {0: x, 1: y, 2: p}.__getitem__)
        lb = all(any(all(not rho(x, y) or subset(y, b) for y in domain)
                         for b in domain) for x in domain)
        hull = any(
            all(not ((empty(x) or relation(x, c)) and rho(x, y)) or relation(y, c)
                for x, y in product(domain, repeat=2))
            and all(not relation(y, c) or any(rho(x, y) for x in domain)
                    for y in domain)
            for c in domain)
        if lb and not (union and hull):
            return False
    return True


def check_refutation(candidate):
    if (not isinstance(candidate, dict) or set(candidate) != {'matrices', 'proof'}
            or not isinstance(candidate['matrices'], list)
            or not isinstance(candidate['proof'], list)):
        raise ValueError('candidate must contain exactly matrices and proof lists')
    theory = [axiom(m) for m in candidate['matrices']]
    lines = k.check_certificate({'instructions': candidate['proof']}, theory)
    if not lines or lines[-1] != k.BOT:
        raise ValueError('only reconstructed genuine falsity is a refutation')
    return {'accepted': True, 'theory': 'EPSC1+BU fused schema',
            'schema_instances': len(theory), 'proof_lines': len(lines)}


def accepts_bytes(data):
    """Fixed unary+BU entry; host resource failures propagate as errors."""
    try:
        check_refutation(decode_candidate(data))
        return True
    except (ValueError, TypeError, KeyError, UnicodeError):
        return False


def search():
    """Ideal fair search for this particular theory; no input or fuel bound.

    Do not confuse this with fixed_theory.search(alternative=True), which
    retains source28's separate EPSC2 comparison interface.
    """
    n = 0
    while True:
        if accepts_bytes(shortlex_bytes_at(n)):
            return n
        n += 1
