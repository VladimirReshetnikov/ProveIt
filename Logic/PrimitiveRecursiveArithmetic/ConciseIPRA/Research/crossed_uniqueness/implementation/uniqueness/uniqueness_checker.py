#!/usr/bin/env python3
"""Strict reference checker for normalized crossed-uniqueness iPRA.

Terms: a natural-number de Bruijn index; ["z"]; ["s", t];
       ["i", counter, seed, body] (body binds index 0).
Formulas: ["=", s, t]; ["q", body]; ["d", body].
Q binds index 0. D binds y at 0 and x at 1.

The six proof forms are hyp, refl, qe, de, di, u. The u payload is
["u", f, a, h, n, base_proof, step_proof]. Both f and h bind index 0.
The recurrence eigenvariable is introduced by the checker, never by input.

The CLI checks a sequent record with exactly the keys scope, context, goal,
proof. A closed theorem has scope 0 and context []. Malformed inputs reject.
No size-frontier claim is made. Runtime resource exhaustion is rejection,
not acceptance. Normalization is part of the trusted implementation.
"""

import json
import sys
from functools import cache


class Invalid(Exception):
    pass


Z = ("z",)


def S(t):
    return ("s", t)


def I(n, a, h):
    return ("i", n, a, h)


def Eq(s, t):
    return ("=", s, t)


def Q(b):
    return ("q", b)


def D(b):
    return ("d", b)


def require(condition):
    if not condition:
        raise Invalid("invalid certificate")


def term(t, scope):
    """Validate the exact term grammar and its numerical scope."""
    if type(t) is int:
        require(0 <= t < scope)
        return t
    require(type(t) in (list, tuple) and len(t) > 0)
    if len(t) == 1 and t[0] == "z":
        return Z
    if len(t) == 2 and t[0] == "s":
        return S(term(t[1], scope))
    if len(t) == 4 and t[0] == "i":
        return I(term(t[1], scope), term(t[2], scope),
                 term(t[3], scope + 1))
    raise Invalid("bad term")


def formula(a, scope):
    """Validate Eq/Q/D, including both binding positions of D."""
    require(type(a) in (list, tuple) and len(a) > 0)
    if len(a) == 3 and a[0] == "=":
        return Eq(term(a[1], scope), term(a[2], scope))
    if len(a) == 2 and a[0] in ("q", "d"):
        return (a[0], formula(a[1], scope + (1 if a[0] == "q" else 2)))
    raise Invalid("bad formula")


def lift_t(t, amount=1, cutoff=0):
    if type(t) is int:
        return t + amount if t >= cutoff else t
    if t[0] == "z":
        return t
    if t[0] == "s":
        return S(lift_t(t[1], amount, cutoff))
    return I(lift_t(t[1], amount, cutoff),
             lift_t(t[2], amount, cutoff),
             lift_t(t[3], amount, cutoff + 1))


def lift_f(a, amount=1, cutoff=0):
    if a[0] == "=":
        return Eq(lift_t(a[1], amount, cutoff),
                  lift_t(a[2], amount, cutoff))
    return (a[0], lift_f(a[1], amount,
                        cutoff + (1 if a[0] == "q" else 2)))


def sub_t(t, images, depth=0):
    """Simultaneously open the first len(images) outer variables."""
    if type(t) is int:
        if t < depth:
            return t
        if t < depth + len(images):
            return lift_t(images[t - depth], depth)
        return t - len(images)
    if t[0] == "z":
        return t
    if t[0] == "s":
        return S(sub_t(t[1], images, depth))
    return I(sub_t(t[1], images, depth), sub_t(t[2], images, depth),
             sub_t(t[3], images, depth + 1))


def sub_f(a, images, depth=0):
    if a[0] == "=":
        return Eq(sub_t(a[1], images, depth), sub_t(a[2], images, depth))
    return (a[0], sub_f(a[1], images,
                       depth + (1 if a[0] == "q" else 2)))


@cache
def nf_t(t):
    if type(t) is int or t[0] == "z":
        return t
    if t[0] == "s":
        return S(nf_t(t[1]))
    n, a, h = nf_t(t[1]), nf_t(t[2]), nf_t(t[3])
    if n == Z:
        return a
    if type(n) is tuple and n[0] == "s":
        return nf_t(sub_t(h, (nf_t(I(n[1], a, h)),)))
    return I(n, a, h)


def nf_f(a):
    if a[0] == "=":
        return Eq(nf_t(a[1]), nf_t(a[2]))
    return (a[0], nf_f(a[1]))


def uses_t(t, index=0):
    if type(t) is int:
        return t == index
    if t[0] == "z":
        return False
    if t[0] == "s":
        return uses_t(t[1], index)
    return (uses_t(t[1], index) or uses_t(t[2], index)
            or uses_t(t[3], index + 1))


def uses_f(a, index=0):
    if a[0] == "=":
        return uses_t(a[1], index) or uses_t(a[2], index)
    return uses_f(a[1], index + (1 if a[0] == "q" else 2))


def infer(p, scope=0, context=()):
    """Infer the normalized conclusion, rejecting every malformed proof."""
    require(type(p) in (list, tuple) and len(p) > 0)
    tag = p[0]
    if tag == "hyp" and len(p) == 2:
        require(type(p[1]) is int and 0 <= p[1] < len(context))
        return context[p[1]]
    if tag == "refl" and len(p) == 2:
        t = nf_t(term(p[1], scope))
        return Eq(t, t)
    if tag == "qe" and len(p) == 4:
        major = infer(p[1], scope, context)
        require(major[0] == "q")
        require(infer(p[2], scope, context) == nf_f(sub_f(major[1], (Z,))))
        t = term(p[3], scope)
        return nf_f(sub_f(major[1], (t,)))
    if tag == "de" and len(p) == 3:
        major = infer(p[1], scope, context)
        require(major[0] == "d")
        opened = tuple(lift_f(a) for a in context) + (Q(major[1]),)
        result = infer(p[2], scope + 1, opened)
        require(not uses_f(result))
        return sub_f(result, (Z,))
    if tag == "di" and len(p) == 4:
        b = formula(p[1], scope + 2)
        t = term(p[2], scope)
        base = nf_f(sub_f(b, (Z, t)))
        raised = lift_f(b, cutoff=2)
        step = nf_f(sub_f(raised, (S(0), lift_t(t))))
        opened = tuple(lift_f(a) for a in context) + (lift_f(base),)
        require(infer(p[3], scope + 1, opened) == step)
        return D(nf_f(b))
    if tag == "u" and len(p) == 7:
        f = term(p[1], scope + 1)
        a = term(p[2], scope)
        h = term(p[3], scope + 1)
        n = term(p[4], scope)
        initial = nf_f(Eq(sub_t(f, (Z,)), a))
        require(infer(p[5], scope, context) == initial)
        # The eigenvariable is new index 0; every passive parameter is
        # shifted past it. Neither a, n nor passive parameters of h can
        # refer to this newly allocated variable.
        f1, h1 = lift_t(f, cutoff=1), lift_t(h, cutoff=1)
        step = nf_f(Eq(sub_t(f1, (S(0),)),
                       sub_t(h1, (sub_t(f1, (0,)),))))
        require(infer(p[6], scope + 1,
                      tuple(lift_f(b) for b in context)) == step)
        return nf_f(Eq(I(n, a, h), sub_t(f, (n,))))
    raise Invalid("bad proof rule")


def check(record):
    require(type(record) is dict and set(record) ==
            {"scope", "context", "goal", "proof"})
    scope = record["scope"]
    require(type(scope) is int and scope >= 0)
    require(type(record["context"]) is list)
    context = tuple(nf_f(formula(a, scope)) for a in record["context"])
    goal = nf_f(formula(record["goal"], scope))
    require(infer(record["proof"], scope, context) == goal)
    return True


if __name__ == "__main__":
    try:
        check(json.load(sys.stdin))
    except (Invalid, RecursionError, MemoryError, ValueError, TypeError,
            IndexError, KeyError, OverflowError):
        print("REJECT")
        sys.exit(1)
    print("ACCEPT")
